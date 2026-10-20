// ==UserScript==
// @name         yellowtv auto-skip
// @namespace    https://github.com/alrti112-cmyk/yellowtv-releases
// @version      2026.10.20
// @description  Clicks skip/close buttons on overlays and ads, hides ad banners. Same engine as the yellowtv app.
// @match        *://*/*
// @run-at       document-start
// @grant        none
// @updateURL    https://raw.githubusercontent.com/alrti112-cmyk/yellowtv-releases/main/yellowtv.user.js
// @downloadURL  https://raw.githubusercontent.com/alrti112-cmyk/yellowtv-releases/main/yellowtv.user.js
// ==/UserScript==

/**
 * yellowtv auto-skip engine.
 *
 * Runs in an isolated world (page JS cannot see or tamper with it) but shares
 * the DOM, so MutationObserver / click() work normally. Also loadable from
 * Node (jsdom) for tests.
 *
 *   const s = YellowTVAutoSkip.start(window, config);  // -> { stop, scanNow, stats }
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.YellowTVAutoSkip = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  const DEFAULTS = {
    selectors: [],            // explicit site rules: clicked without label check
    heuristics: true,         // also match generic skip/close buttons by label
    labelsSkip: ['skip', 'skip ad', 'skip ads', 'skip now', 'skip intro', '건너뛰기', '광고 건너뛰기', '스킵'],
    labelsClose: ['close', 'dismiss', 'close ad', '닫기', '광고 닫기', '×', '✕', '✖'],
    requireVideoContext: true, // heuristic matches must overlap a <video> rect
    checkLayout: true,         // false only in jsdom (no layout engine)
    fullPointerSequence: false,// dispatch pointer/mouse events before click()
    debounceMs: 50,
    minScanGapMs: 200,         // never scan more often than this (busy pages like YouTube mutate constantly)
    retryMs: 250,              // re-check found-but-not-yet-clickable candidates
    pendingTimeoutMs: 15000,
    cooldownMs: 1500,          // per element
    maxClicksPerElement: 3,
    maxClicksPer10s: 20,       // global brake against re-render loops
    onClick: null,             // (info) => void
    hideAdFrames: false,       // hide off-site iframes / ad containers that have a standard ad-banner size (728x90, 300x250, ...)
    hideLinkedBanners: false,  // hide banner-shaped images/videos wrapped in a link to ANOTHER site (typical ad banners)
    nativeClick: null,         // (x, y) => void : ask the host app for a real (trusted) mouse click; top frame only
    adFastForward: null,       // {adSelector, videoSelector}: speed through ad playback when no button exists
    debug: false,              // console.log what was found / why it was not clicked
  };

  const CANDIDATE_SEL =
    'button,[role="button"],a,input[type="button"],[aria-label],[title],' +
    '[class*="skip" i],[class*="close" i],[id*="skip" i],[id*="close" i]';

  const norm = (s) =>
    String(s || '')
      .toLowerCase()
      .replace(/[\s​]+/g, ' ')
      .replace(/[\s›»>→▶▷⏭.…]+$/u, '') // "Skip Ad ›" -> "skip ad"
      .trim();

  // Small heuristic for the registrable domain (same idea as the desktop guard).
  const MULTI_TLD = new Set(['co.kr', 'or.kr', 'ne.kr', 'go.kr', 'co.uk', 'org.uk', 'com.au', 'co.jp', 'com.br', 'com.cn']);
  function siteOf(hostname) {
    const p = String(hostname).toLowerCase().split('.');
    if (p.length <= 2) return p.join('.');
    const last2 = p.slice(-2).join('.');
    return MULTI_TLD.has(last2) ? p.slice(-3).join('.') : last2;
  }

  function createAutoSkipper(win, userCfg) {
    const cfg = Object.assign({}, DEFAULTS, userCfg || {});
    const doc = win.document;
    const skipSet = new Set(cfg.labelsSkip.map(norm));
    const closeSet = new Set(cfg.labelsClose.map(norm));
    const explicitSel = (cfg.selectors || []).join(',');

    const clicks = new WeakMap();        // el -> {count, last}
    const observed = new WeakSet();      // roots (document / shadowRoots)
    const pending = new Map();           // el -> firstSeen ts
    const recentClicks = [];
    const stats = { clicked: 0, scans: 0, skippedOffsite: 0, hiddenBanners: 0 };

    let dirty = new Set();
    let flushTimer = null;
    let lastFlush = 0;
    let retryTimer = null;
    let stopped = false;
    const observers = [];

    // ---------- candidate discovery ----------
    function collect(node, out, skipShadow) {
      if (!node || (node.nodeType !== 1 && node.nodeType !== 11 && node.nodeType !== 9)) return;
      if (node.nodeType === 1) {
        if (explicitSel && node.matches(explicitSel)) out.add(node);
        if (cfg.heuristics) {
          const c = node.closest && node.closest(CANDIDATE_SEL); // text changed inside a button
          if (c) out.add(c);
        }
      }
      const q = node.querySelectorAll ? node : null;
      if (q) {
        if (explicitSel) q.querySelectorAll(explicitSel).forEach((e) => out.add(e));
        if (cfg.heuristics) q.querySelectorAll(CANDIDATE_SEL).forEach((e) => out.add(e));
        // open shadow roots: observe + descend
        if (!skipShadow) q.querySelectorAll('*').forEach((e) => {
          if (e.shadowRoot) {
            observeRoot(e.shadowRoot);
            collect(e.shadowRoot, out);
          }
        });
      }
      if (node.nodeType === 1 && node.shadowRoot) {
        observeRoot(node.shadowRoot);
        collect(node.shadowRoot, out);
      }
    }

    // ---------- classification ----------
    function labelOf(el) {
      return norm(
        el.getAttribute('aria-label') || el.getAttribute('title') || el.value || el.textContent
      );
    }

    function classify(el) {
      if (explicitSel && el.matches(explicitSel)) return 'rule';
      if (!cfg.heuristics) return null;
      const raw = el.getAttribute('aria-label') || el.getAttribute('title') || el.value || el.textContent || '';
      if (raw.length > 40) return null; // real buttons are short; avoids matching containers
      const label = norm(raw);
      if (skipSet.has(label)) return 'skip';
      if (closeSet.has(label)) return 'close';
      return null;
    }

    function overlapsVideo(el) {
      const r = el.getBoundingClientRect();
      const vids = doc.querySelectorAll('video');
      for (const v of vids) {
        const b = v.getBoundingClientRect();
        if (b.width < 50 || b.height < 50) continue;
        if (r.right >= b.left && r.left <= b.right && r.bottom >= b.top && r.top <= b.bottom) return true;
      }
      return false;
    }

    // Returns null when clickable, otherwise a short reason string.
    function whyNot(el) {
      if (!el.isConnected) return 'detached';
      if (el.disabled || el.getAttribute('aria-disabled') === 'true') return 'disabled';
      if (el.hasAttribute('inert')) return 'inert';
      if (!cfg.checkLayout) return null;
      const cs = win.getComputedStyle(el);
      if (cs.display === 'none') return 'display:none';
      if (cs.visibility === 'hidden') return 'visibility:hidden';
      if (cs.pointerEvents === 'none') return 'pointer-events:none';
      if (parseFloat(cs.opacity) === 0) return 'opacity:0';
      const r = el.getBoundingClientRect();
      if (r.width < 1 || r.height < 1) return 'zero-size';
      if (r.bottom < 0 || r.right < 0 || r.top > win.innerHeight || r.left > win.innerWidth) return 'offscreen';
      const x = Math.min(Math.max(r.left + r.width / 2, 0), win.innerWidth - 1);
      const y = Math.min(Math.max(r.top + r.height / 2, 0), win.innerHeight - 1);
      const top = (el.getRootNode().elementFromPoint || doc.elementFromPoint).call(el.getRootNode(), x, y);
      if (!top) return 'no-hit-target';
      return top === el || el.contains(top) || top.contains(el) ? null : 'covered-by:' + top.tagName + '.' + top.className;
    }
    const isInteractable = (el) => whyNot(el) === null;

    function leavesSite(el) {
      if (el.tagName !== 'A' || !el.getAttribute('href')) return false;
      try {
        const u = new win.URL(el.href, win.location.href);
        if (u.protocol === 'javascript:' || u.hash && u.pathname === win.location.pathname) return false;
        return u.origin !== win.location.origin;
      } catch (_) {
        return true;
      }
    }

    // ---------- action ----------
    function allowedByBudget(el) {
      const now = Date.now();
      const st = clicks.get(el);
      if (st && (st.count >= cfg.maxClicksPerElement || now - st.last < cfg.cooldownMs)) return false;
      while (recentClicks.length && now - recentClicks[0] > 10000) recentClicks.shift();
      return recentClicks.length < cfg.maxClicksPer10s;
    }

    function fire(el, kind) {
      if (leavesSite(el)) { // never follow a sponsor link by accident
        stats.skippedOffsite++;
        return false;
      }
      if (cfg.fullPointerSequence) {
        const r = el.getBoundingClientRect();
        const init = { bubbles: true, cancelable: true, view: win, clientX: r.left + r.width / 2, clientY: r.top + r.height / 2 };
        for (const t of ['pointerdown', 'mousedown', 'pointerup', 'mouseup']) {
          const Ctor = t.startsWith('pointer') && win.PointerEvent ? win.PointerEvent : win.MouseEvent;
          el.dispatchEvent(new Ctor(t, init));
        }
      }
      const prior = (clicks.get(el) || { count: 0 }).count;
      let how = 'el.click';
      if (cfg.nativeClick && prior === 0 && win.top === win) {
        const r = el.getBoundingClientRect();
        cfg.nativeClick(Math.round(r.left + r.width / 2), Math.round(r.top + r.height / 2));
        how = 'native';
      } else {
        el.click();
      }
      if (cfg.debug) console.log('[yellowtv] CLICKED via', how, kind, JSON.stringify(labelOf(el)), el.className);
      const now = Date.now();
      const st = clicks.get(el) || { count: 0, last: 0 };
      st.count++; st.last = now;
      clicks.set(el, st);
      recentClicks.push(now);
      stats.clicked++;
      if (cfg.onClick) {
        try { cfg.onClick({ kind, label: labelOf(el), tag: el.tagName, host: win.location.host }); } catch (_) {}
      }
      return true;
    }

    function process(el, now) {
      const kind = classify(el);
      if (!kind) { pending.delete(el); return; }
      if (kind !== 'rule' && cfg.requireVideoContext && cfg.checkLayout && !overlapsVideo(el)) {
        pending.delete(el); return;
      }
      const why = whyNot(el);
      if (why) { // present but not clickable yet: keep watching
        if (!pending.has(el)) {
          pending.set(el, now);
          if (cfg.debug) console.log('[yellowtv] found', kind, JSON.stringify(labelOf(el)), '- waiting:', why);
        }
        return;
      }
      pending.delete(el);
      if (allowedByBudget(el)) fire(el, kind);
    }

    // ---------- banner hiding ----------
    function isOffsiteHref(a) {
      try {
        const u = new win.URL(a.href, win.location.href);
        return /^https?:$/.test(u.protocol) && siteOf(u.hostname) !== siteOf(win.location.hostname);
      } catch (_) {
        return false;
      }
    }

    function bannerShaped(m) {
      if (!cfg.checkLayout) return true;
      const r = m.getBoundingClientRect();
      return r.width >= 250 && r.height >= 40 && r.height <= 200 && r.width / r.height >= 2.2;
    }

    const AD_SIZES = [[728, 90], [970, 90], [970, 250], [970, 66], [468, 60], [320, 50], [320, 100], [300, 250], [300, 600], [336, 280], [160, 600], [120, 600], [250, 250], [300, 50], [234, 60], [120, 240], [300, 100], [980, 120], [930, 180], [750, 100], [750, 200]];
    const isAdSize = (r) => AD_SIZES.some(([w, h]) => Math.abs(r.width - w) <= 3 && Math.abs(r.height - h) <= 3);
    function hideAdFrames(root) {
      if (!root || !root.querySelectorAll) return;
      const found = [];
      if (root.nodeType === 1 && root.matches && root.matches('iframe, ins.adsbygoogle')) found.push(root);
      root.querySelectorAll('iframe, ins.adsbygoogle').forEach((f) => found.push(f));
      for (const f of found) {
        if (f.hasAttribute('data-yellowtv-hidden')) continue;
        let ad = f.tagName === 'INS';
        if (!ad) {
          try {
            const u = new win.URL(f.src || '', win.location.href);
            if (!f.src || !/^https?:$/.test(u.protocol) || siteOf(u.hostname) === siteOf(win.location.hostname)) continue;
          } catch (_) { continue; }
          ad = isAdSize(f.getBoundingClientRect());
        }
        if (!ad) continue;
        const par = f.parentElement;
        const box = par && par.children.length === 1 && !/^(BODY|HTML|MAIN)$/.test(par.tagName) ? par : f; // an otherwise empty wrapper goes too
        box.style.setProperty('display', 'none', 'important');
        f.setAttribute('data-yellowtv-hidden', '1');
        stats.hiddenBanners++;
        if (cfg.debug) console.log('[yellowtv] hid ad frame ->', f.src || f.className);
      }
    }
    function hideBanners(root) {
      if (!root || !root.querySelectorAll) return;
      const media = [];
      if (root.nodeType === 1 && root.matches && root.matches('img,video')) media.push(root);
      root.querySelectorAll('a[href] img, a[href] video').forEach((m) => media.push(m));
      for (const m of media) {
        const a = m.closest('a[href]');
        if (!a || a.hasAttribute('data-yellowtv-hidden')) continue;
        if (a.textContent.trim().length > 40) continue;   // a card with real text, not a pure banner
        if (!isOffsiteHref(a) || !bannerShaped(m)) continue;
        a.style.setProperty('display', 'none', 'important');
        a.setAttribute('data-yellowtv-hidden', '1');
        stats.hiddenBanners++;
        if (cfg.debug) console.log('[yellowtv] hid banner ->', a.href);
      }
    }

    // ---------- scheduling ----------
    function flush() {
      flushTimer = null;
      if (stopped) return;
      lastFlush = Date.now();
      stats.scans++;
      const out = new Set();
      if (cfg.hideLinkedBanners) (dirty.size > 300 ? [doc] : [...dirty]).forEach(hideBanners);
      if (cfg.hideAdFrames) (dirty.size > 300 ? [doc] : [...dirty]).forEach(hideAdFrames);
      if (dirty.size > 300) collect(doc, out, true); // storm: rescan without the costly shadow-root walk
      else dirty.forEach((n) => collect(n, out));
      dirty = new Set();
      const now = Date.now();
      out.forEach((el) => process(el, now));
      schedulePendingRetry();
    }

    function schedule() {
      if (!flushTimer && !stopped) {
        const wait = Math.max(cfg.debounceMs, cfg.minScanGapMs - (Date.now() - lastFlush));
        flushTimer = win.setTimeout(flush, wait);
      }
    }

    function schedulePendingRetry() {
      if (retryTimer || !pending.size || stopped) return;
      retryTimer = win.setTimeout(() => {
        retryTimer = null;
        const now = Date.now();
        for (const [el, since] of pending) {
          if (now - since > cfg.pendingTimeoutMs || !el.isConnected) pending.delete(el);
          else process(el, now);
        }
        schedulePendingRetry();
      }, cfg.retryMs);
    }

    function observeRoot(r) {
      if (observed.has(r) || stopped) return;
      observed.add(r);
      const mo = new win.MutationObserver((muts) => {
        for (const m of muts) {
          if (m.type === 'childList') m.addedNodes.forEach((n) => dirty.add(n.nodeType === 1 ? n : m.target)); // text swap -> re-scan its element
          else if (m.type === 'characterData') dirty.add(m.target.parentElement || m.target.parentNode);
          else dirty.add(m.target); // attribute flips (disabled, class, style, aria-*)
        }
        schedule();
      });
      mo.observe(r, {
        childList: true,
        subtree: true,
        characterData: true,
        attributes: true,
        attributeFilter: ['class', 'style', 'hidden', 'disabled', 'aria-disabled', 'aria-hidden', 'aria-label', 'title'],
      });
      observers.push(mo);
    }

    // ---------- ad playback fast-forward (for ads that have no skip button) ----------
    let adSaved = null;
    let adTimer = null;
    function adTick() {
      const ff = cfg.adFastForward;
      const video = doc.querySelector(ff.videoSelector || 'video');
      const inAd = !!(video && doc.querySelector(ff.adSelector));
      if (inAd) {
        if (!adSaved) {
          adSaved = { muted: video.muted, rate: video.playbackRate };
          if (cfg.debug) console.log('[yellowtv] ad playback detected, fast-forwarding');
        }
        video.muted = true;
        video.playbackRate = 16;
        if (isFinite(video.duration) && video.duration > 0 && video.currentTime < video.duration - 0.1) {
          video.currentTime = video.duration - 0.05;
          stats.adSeeks = (stats.adSeeks || 0) + 1;
        }
      } else if (adSaved) { // ad ended: restore the user's own audio/speed
        if (video) { video.muted = adSaved.muted; video.playbackRate = adSaved.rate; }
        adSaved = null;
      }
    }
    if (cfg.adFastForward && cfg.adFastForward.adSelector) adTimer = win.setInterval(adTick, 200);

    function scanNow() {
      dirty.add(doc);
      flush();
    }

    if (cfg.debug) console.log('[yellowtv] engine started on', win.location.href, 'rules:', (cfg.selectors || []).length);
    // images report their size only after loading; 'load' doesn't bubble, so listen in the capture phase
    if (cfg.hideLinkedBanners || cfg.hideAdFrames) doc.addEventListener('load', (e) => { if (e.target && ['IMG', 'IFRAME'].includes(e.target.tagName)) { dirty.add(e.target); schedule(); } }, true);
    observeRoot(doc);
    scanNow();

    return {
      stats,
      scanNow,
      stop() {
        stopped = true;
        observers.forEach((o) => o.disconnect());
        if (flushTimer) win.clearTimeout(flushTimer);
        if (retryTimer) win.clearTimeout(retryTimer);
        if (adTimer) win.clearInterval(adTimer);
        pending.clear();
      },
    };
  }

  return {
    start: createAutoSkipper,
    createAutoSkipper,
    DEFAULTS,
    _norm: norm,
  };
});

// Picks the per-site config (same rules/sites.json as the desktop app) and starts the engine.
// The two placeholder tokens below are replaced by MainActivity before injection.
(function () {
  if (window.__yellowtvBooted) return;
  window.__yellowtvBooted = true;
  var SITES = {
  "_comment": "host: exact or '*.suffix'. selectors are clicked as-is (no label check). Verify selectors against the live site; they change.",
  "defaults": {
    "heuristics": true,
    "hideLinkedBanners": true,
    "hideAdFrames": true,
    "labelsSkip": ["skip", "skip ad", "skip ads", "skip now", "skip intro", "건너뛰기", "광고 건너뛰기", "스킵"],
    "labelsClose": ["close", "dismiss", "close ad", "닫기", "광고 닫기", "×", "✕", "✖"]
  },
  "sites": [
    {
      "hosts": ["*.youtube.com"],
      "selectors": [
        ".ytp-ad-skip-button",
        ".ytp-ad-skip-button-modern",
        ".ytp-skip-ad-button",
        ".ytp-ad-overlay-close-button"
      ],
      "adFastForward": { "adSelector": ".ad-showing", "videoSelector": "video.html5-main-video" }
    },
    {
      "hosts": ["*"],
      "selectors": [
        ".videoAdUiSkipButton",
        ".jw-skip",
        ".vjs-skip-button",
        "button[aria-label='Skip Ad']",
        "button[aria-label='Close ad']"
      ]
    }
  ]
};
  function hostMatches(p, h) {
    if (p === '*') return true;
    if (p.indexOf('*.') === 0) { var b = p.slice(2); return h === b || h.endsWith('.' + b); }
    return h === p;
  }
  var host = (location.hostname || '').toLowerCase();
  var cfg = Object.assign({}, SITES.defaults, { selectors: [] });
  SITES.sites.forEach(function (s) {
    if (s.hosts.some(function (h) { return hostMatches(h, host); })) {
      cfg.selectors.push.apply(cfg.selectors, s.selectors || []);
      if (s.adFastForward) cfg.adFastForward = s.adFastForward;
    }
  });
  cfg.fullPointerSequence = true; // synthetic click() alone is ignored by some players
  cfg.debug = false;
  if (window.YellowTVAutoSkip) window.YellowTVAutoSkip.start(window, cfg);
})();
