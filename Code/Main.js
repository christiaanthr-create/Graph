// ==UserScript==
// @name         myAIE Auto Grades (Courses page)
// @namespace    http://tampermonkey.net/
// @version      11.0
// @description  Replaces the course cards with results cards: marks, weightings, today's classes (with Join), custom order, PDFs and settings
// @match        https://student.myaie.ac/*
// @run-at       document-start
// @require      https://cdnjs.cloudflare.com/ajax/libs/jspdf/2.5.1/jspdf.umd.min.js
// @grant        none
// ==/UserScript==

(function () {
    'use strict';

    /* =====================================================================
     * CONFIG
     * ===================================================================== */
    const API_BASE = 'https://testapi.myaie.ac/api/v1/';
    const GRADES_API = API_BASE + 'getSubjectAssignments?sid=';
    const SCHEDULE_API = API_BASE + 'getSubjectEventPageWiseTz';
    const JOIN_API = API_BASE + 'joinBBBClass?id=';
    const JSPDF_URL = 'https://cdnjs.cloudflare.com/ajax/libs/jspdf/2.5.1/jspdf.umd.min.js';   // keep in sync with @require

    const EXCLUDE = [];             // course ids to hide from the dashboard
    const PASS_MARK = 50;           // overall % needed to pass a course
    const GRADES_TTL_MS = 5 * 60 * 1000;        // how often a course's marks are refetched
    const SCHEDULE_TTL_MS = 30 * 1000;          // schedule refetch while a class is on today or starts within 2 hours (keeps Join accurate)
    const SCHEDULE_IDLE_TTL_MS = 10 * 60 * 1000; // schedule refetch the rest of the time
    const LOOKAHEAD_DAYS = 14;      // how far ahead to look for the next class
    const SWAP_MS = 280;            // how long a card slides aside while dragging (higher = slower)
    const MAX_PAGES = 10;           // safety limit when paging through the schedule
    const DEBUG = false;            // log extra details to the console

    const KEYS = { grades: 'myAIE_grades_cache_v9', weights: 'myAIE_weights_v2', order: 'myAIE_order_v1', settings: 'myAIE_settings_v1', courses: 'myAIE_courses_v1', sort: 'myAIE_sort_v1' };
    const DEFAULT_SETTINGS = {
        showPercent: true,          // marks, averages and the weighted line
        showWeights: true,          // the (15%) next to each assessment
        showProgress: true,         // the original card's progress bar
        showToday: true,            // the box with today's classes and the next class
        showUpNext: true,           // the UP NEXT banner and highlight
        hiddenCourses: [],          // course ids hidden from the dashboard
        weights: {}                 // your own weightings: { courseId: { assessmentId: % } }
    };
    const SORT_MODES = [
        ['custom', 'My order (drag to arrange)'],
        ['alpha', 'Alphabetical A-Z'],
        ['alphaDesc', 'Alphabetical Z-A'],
        ['avgDesc', 'Average grade: high to low'],
        ['avgAsc', 'Average grade: low to high'],
        ['exams', 'Upcoming exams: soonest first']
    ];
    const WEIGHT_RANGE = { from: '2026-01-01T00:00:00.000Z', to: '2027-12-31T23:59:59.999Z' };
    const HOUR = 3600 * 1000;

    // One palette for the page and the PDF ([r, g, b])
    const P = {
        green: [67, 178, 117], red: [217, 83, 79], teal: [59, 180, 194], blue: [45, 100, 173],
        text: [52, 58, 64], grey: [108, 117, 125], border: [222, 226, 230], navy: [31, 36, 80]
    };
    const rgb = (c, a) => a === undefined ? `rgb(${c.join(',')})` : `rgba(${c.join(',')},${a})`;

    /* =====================================================================
     * STATE
     * ===================================================================== */
    let TOKEN = null;               // login token, kept in memory only and never saved
    let WEIGHTS = readJSON(KEYS.weights, {});   // sid -> { at, ttl, map: { assessmentId: weight% } }
    let SETTINGS = normalizeSettings(readJSON(KEYS.settings, {}));
    let SORT = sanitizeSort(readJSON(KEYS.sort, 'custom'));   // how the course cards are ordered
    const schedule = {};            // sid -> { items: today's classes + assessments, next: next class }
    const fetchedAt = { grades: {}, schedule: {} };   // kind -> sid -> time of last fetch
    const headerHeights = {};       // sid -> height of the original card header (only measurable while the originals are visible)
    const emptySids = new Set();    // courses the API says have no assessments

    let running = false;            // a refresh is in progress
    let statusText = '';
    let renderedSig = '';           // which cards the current render was built from
    let lastGridKey = '', lastHeaderKey = '';   // what is on screen, so unchanged parts are left alone
    let dragging = false;
    let swapUntil = 0;              // drag swaps are paused until this time so the slide can finish
    let retryTimer = null, renderTimer = null, modalKeyHandler = null;

    /* =====================================================================
     * UTILITIES
     * ===================================================================== */
    function readJSON(key, fallback) {
        try { return JSON.parse(localStorage.getItem(key)) || fallback; } catch (e) { return fallback; }
    }
    const writeJSON = (key, value) => localStorage.setItem(key, JSON.stringify(value));

    // Coerces whatever is in storage into valid settings, so a corrupted value can't break the page
    function normalizeSettings(raw) {
        const out = JSON.parse(JSON.stringify(DEFAULT_SETTINGS));
        const r = raw && typeof raw === 'object' ? raw : {};
        Object.keys(out).forEach(k => { if (typeof out[k] === 'boolean' && typeof r[k] === 'boolean') out[k] = r[k]; });
        if (Array.isArray(r.hiddenCourses)) out.hiddenCourses = r.hiddenCourses.map(Number).filter(Boolean);
        if (r.weights && typeof r.weights === 'object') {
            Object.entries(r.weights).forEach(([sid, mine]) => {
                const clean = {};
                Object.entries(mine && typeof mine === 'object' ? mine : {}).forEach(([aid, v]) => { if (v !== '' && v !== null && Number.isFinite(+v)) clean[aid] = +v; });
                if (Object.keys(clean).length) out.weights[sid] = clean;
            });
        }
        return out;
    }

    function sanitizeSort(mode) { return SORT_MODES.some(([k]) => k === mode) ? mode : 'custom'; }
    const log = (...a) => { if (DEBUG) console.log('[myAIE]', ...a); };

    const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
    const r1 = n => Math.round(n * 10) / 10;
    const pad2 = n => String(n).padStart(2, '0');
    const dateKey = d => d.getFullYear() + '-' + pad2(d.getMonth() + 1) + '-' + pad2(d.getDate());
    const mean = arr => arr.reduce((a, b) => a + b, 0) / arr.length;
    const fmtAvg = (marks, empty = 'N/A') => marks.length ? r1(mean(marks)) + '%' : empty;
    const shortName = n => String(n).replace(/^.*?\s+-\s+/, '').trim() || String(n);
    const isScored = r => r.graded && r.pct !== null;                // has a score
    const isFuture = r => r.opens > Date.now() / 1000;               // hasn't taken place yet
    const isMarked = r => isScored(r) && !isFuture(r);               // counts toward averages

    const loadGrades = () => readJSON(KEYS.grades, {});
    const loadOrder = () => readJSON(KEYS.order, []);

    /* =====================================================================
     * NETWORK: capture the site's login token and responses
     * ===================================================================== */
    const origFetch = window.fetch;

    function grabAuth(headers) {
        try {
            if (!headers) return;
            let v;
            if (typeof Headers !== 'undefined' && headers instanceof Headers) v = headers.get('authorization');
            else if (Array.isArray(headers)) { const f = headers.find(x => String(x[0]).toLowerCase() === 'authorization'); v = f && f[1]; }
            else for (const k in headers) if (k.toLowerCase() === 'authorization') v = headers[k];
            if (v && /^Bearer\s/i.test(v)) TOKEN = v;
        } catch (e) {}
    }

    function tokenFromStorage() {
        try {
            for (let i = 0; i < localStorage.length; i++) {
                const m = String(localStorage.getItem(localStorage.key(i))).match(/eyJ[\w-]+\.[\w-]+\.[\w-]+/);
                if (m) return 'Bearer ' + m[0];
            }
        } catch (e) {}
        return null;
    }

    const isGradesUrl = url => /getSubjectAssignments/.test(String(url || ''));

    function sidFromUrl(url) {
        const m = String(url || '').match(/getSubjectAssignments\?[^#]*sid=(\d+)/);
        return m ? +m[1] : null;
    }

    // Authenticated request to the myAIE API (uses the real fetch, so it isn't captured again)
    function api(url, init = {}) {
        if (!TOKEN) TOKEN = tokenFromStorage();
        if (!TOKEN) return Promise.reject(new Error('you are not logged in yet'));
        return origFetch(url, { ...init, headers: { Authorization: TOKEN, Accept: 'application/json', ...init.headers } });
    }

    window.fetch = function (input, init) {
        let url = '';
        try {
            url = input && input.url ? input.url : String(input);
            if (/myaie\.ac/.test(url)) { grabAuth(init && init.headers); if (input && input.headers) grabAuth(input.headers); }
        } catch (e) {}
        const p = origFetch.apply(this, arguments);
        if (isGradesUrl(url)) {                                      // only the grades responses are worth reading
            p.then(res => {
                try { res.clone().json().then(j => { if (storeGrades(j, sidFromUrl(url))) renderSoon(); }).catch(() => {}); } catch (e) {}
            }).catch(() => {});
        }
        return p;
    };

    const xhr = XMLHttpRequest.prototype;
    const xOpen = xhr.open, xSetHeader = xhr.setRequestHeader, xSend = xhr.send;
    xhr.open = function (method, url) { this.__myaieUrl = url; return xOpen.apply(this, arguments); };
    xhr.setRequestHeader = function (name, value) {
        if (String(name).toLowerCase() === 'authorization' && /^Bearer\s/i.test(value)) TOKEN = value;
        return xSetHeader.apply(this, arguments);
    };
    xhr.send = function () {
        this.addEventListener('load', () => {
            if (!isGradesUrl(this.__myaieUrl)) return;
            try {
                let j = null;
                if (this.responseType === 'json') j = this.response;
                else if (this.responseType === '' || this.responseType === 'text') j = JSON.parse(this.responseText);
                if (j && storeGrades(j, sidFromUrl(this.__myaieUrl))) renderSoon();
            } catch (e) {}
        });
        return xSend.apply(this, arguments);
    };

    /* =====================================================================
     * DATA: grades, schedule, weightings
     * ===================================================================== */
    // Saves a getSubjectAssignments response. Returns true if the response was one of ours.
    function storeGrades(json, sidHint) {
        const list = Array.isArray(json) ? json : (Array.isArray(json && json.data) ? json.data : null);
        if (!list) return false;
        if (!list.length) { if (sidHint) emptySids.add(+sidHint); return true; }

        const first = list[0];
        if (!first || first.studentCourses === undefined || first.assessment_id === undefined) return false;
        const sid = +(sidHint || (first.assignedCourses && first.assignedCourses[0] && first.assignedCourses[0].id) || 0);
        if (!sid) return false;

        const entry = { code: first.code || String(first.courseId), courseName: first.course_name || '', rows: {} };
        list.forEach(a => {
            const sc = (a.studentCourses && a.studentCourses[0]) || {};
            const graded = sc.mark !== null && sc.mark !== undefined;   // an unmarked assessment reports "0%", so check mark
            const total = parseFloat(sc.ass_total_mark ?? a.subAssTotMark);
            const got = parseFloat(sc.subAssObtainMark);
            const pct = graded ? parseFloat(sc.subAssObtainPercentage) : null;
            entry.rows[a.assessment_id] = {
                id: a.assessment_id, name: a.name, type: a.ass_type, graded, opens: a.open_date_time || 0, closes: a.close_date_time || 0,
                got: graded ? r1(got) : null,
                total: isNaN(total) ? null : r1(total),
                pct: pct === null || isNaN(pct) ? null : r1(pct),
                result: graded ? (sc.pass_status === 'FAIL' ? 'Fail' : 'Pass') : (a.status || 'Pending')
            };
        });

        const data = loadGrades();
        data[sid] = entry;
        writeJSON(KEYS.grades, data);
        emptySids.delete(sid);
        return true;
    }

    // One page of the schedule endpoint for a course
    async function postSchedule(sid, { page = 1, listType = 'upcoming', from, to }) {
        const r = await api(SCHEDULE_API, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
                subjectId: [String(sid)], pageNumber: page, itemsPerPage: 50, status: listType, filter: 'all',
                startDateListView: from, endDateListView: to
            })
        });
        return r.ok ? r.json() : null;
    }

    const scheduleItems = j => Object.values((j && j.finalArray) || {}).flatMap(arr => arr || []);

    // Today's classes and assessments, plus the next class that hasn't ended
    async function fetchSchedule(sid) {
        try {
            const now = new Date();
            const from = new Date(now.getFullYear(), now.getMonth(), now.getDate());
            const to = new Date(now.getFullYear(), now.getMonth(), now.getDate() + LOOKAHEAD_DAYS, 23, 59, 59, 999);
            const j = await postSchedule(sid, { from: from.toISOString(), to: to.toISOString() });
            if (!j) return;

            const startOf = it => it.class_start_dt || it.open_date_time || 0;
            const items = ((j.finalArray && j.finalArray[dateKey(now)]) || []).slice().sort((x, y) => startOf(x) - startOf(y));
            const nowSec = Date.now() / 1000;
            const next = scheduleItems(j)
                .filter(it => it.category !== 'task' && !it.canceled && !it.is_past && it.class_end_dt > nowSec)
                .sort((x, y) => x.class_start_dt - y.class_start_dt)[0] || null;
            schedule[sid] = { items, next };
        } catch (e) {}
    }

    // Assessment weightings come from the schedule data. Searches the upcoming list, then the past list.
    async function fetchWeights(sid) {
        const cached = WEIGHTS[sid];
        if (cached && Date.now() - cached.at < cached.ttl) return;
        try {
            const map = {}, seen = new Set();
            for (const listType of ['upcoming', 'past']) {
                for (let page = 1; page <= MAX_PAGES; page++) {
                    const j = await postSchedule(sid, { page, listType, ...WEIGHT_RANGE });
                    if (!j) break;
                    let added = 0;
                    scheduleItems(j).forEach(it => {
                        const key = (it.category || '') + ':' + (it.id ?? it.assessment_id);
                        if (seen.has(key)) return;
                        seen.add(key); added++;
                        if (it.category === 'task' && it.assessment_id && it.ass_weighting != null) map[it.assessment_id] = parseFloat(it.ass_weighting);
                    });
                    if (!added) break;
                }
                log('weights after', listType, 'search for course', sid, map);
            }
            WEIGHTS[sid] = { at: Date.now(), ttl: Object.keys(map).length ? 24 * HOUR : 10 * 60 * 1000, map };
            writeJSON(KEYS.weights, WEIGHTS);
            renderSoon();
        } catch (e) {}
    }

    // How long a course's schedule stays fresh: briefly while a class is on or close (keeps Join accurate), longer otherwise
    function scheduleTtl(sid) {
        const sch = schedule[sid];
        if (!sch) return SCHEDULE_TTL_MS;
        const nowSec = Date.now() / 1000;
        const busy = (sch.next && sch.next.class_start_dt - nowSec < 2 * 3600) || sch.items.some(it => it.category !== 'task' && !it.is_past && !it.canceled);
        return busy ? SCHEDULE_TTL_MS : SCHEDULE_IDLE_TTL_MS;
    }
    const isStale = (kind, sid) => Date.now() - (fetchedAt[kind][sid] || 0) >= (kind === 'grades' ? GRADES_TTL_MS : scheduleTtl(sid));

    async function refresh(sids) {
        if (running || !sids.length) return;
        if (!TOKEN) TOKEN = tokenFromStorage();
        if (!TOKEN) {
            if (statusText !== 'Waiting for your login session...') { statusText = 'Waiting for your login session...'; render(); }
            clearTimeout(retryTimer);
            retryTimer = setTimeout(tick, 1500);
            return;
        }

        const wantGrades = sids.filter(sid => isStale('grades', sid));
        const wantSchedule = sids.filter(sid => isStale('schedule', sid));
        if (!wantGrades.length && !wantSchedule.length) return;

        running = true;
        if (wantGrades.length) { statusText = 'Loading grades...'; render(); }
        const startedAt = Date.now();
        wantGrades.forEach(sid => { fetchedAt.grades[sid] = startedAt; });
        wantSchedule.forEach(sid => { fetchedAt.schedule[sid] = startedAt; });

        let failed = 0, authFailed = false;
        await Promise.all(wantGrades.map(async sid => {
            try {
                const r = await api(GRADES_API + sid);
                if (r.status === 401 || r.status === 403) { authFailed = true; return; }
                if (!r.ok) { failed++; return; }
                storeGrades(await r.json(), sid);
            } catch (e) { failed++; }
        }));
        if (!authFailed) await Promise.all([...wantSchedule.map(fetchSchedule), ...sids.map(fetchWeights)]);

        running = false;
        if (authFailed) TOKEN = null;
        if (authFailed) statusText = 'Session expired. Refresh the page or log in again.';
        else if (failed) statusText = failed + ' course(s) failed to load.';
        else if (wantGrades.length) statusText = 'Updated ' + new Date().toLocaleTimeString();
        render();
    }

    async function joinClass(classId, btn) {
        const win = window.open('about:blank', '_blank');       // opened straight away so the popup isn't blocked
        const label = btn.textContent;
        btn.disabled = true; btn.textContent = 'Joining...';
        try {
            const j = await (await api(JOIN_API + encodeURIComponent(classId))).json();
            if (j && !j.error && j.url && /^https:\/\//.test(j.url)) {
                if (win) win.location.href = j.url; else window.location.href = j.url;
            } else {
                if (win) win.close();
                alert((j && (j.message || j.title)) || 'Could not join the class.');
            }
        } catch (e) {
            if (win) win.close();
            alert(/logged in/.test(e && e.message) ? 'You are not logged in yet. Refresh the page and try again.' : 'Could not join the class. Try refreshing the page.');
        }
        btn.disabled = false; btn.textContent = label;
    }

    /* =====================================================================
     * COURSE STATS (shared by the cards, the popup and the PDF)
     * ===================================================================== */
    function courseStats(sid, d) {
        const rows = Object.values(d.rows);
        const marks = rows.filter(isMarked).map(r => r.pct);
        const map = { ...((WEIGHTS[sid] && WEIGHTS[sid].map) || {}), ...(SETTINGS.weights[sid] || {}) };   // your overrides win
        const weightOf = r => (r.id !== undefined && map[r.id] !== undefined) ? map[r.id] : null;

        let totalW = 0, markedW = 0, earned = 0, missing = 0;
        rows.forEach(r => {
            const w = weightOf(r);
            if (w === null) { missing++; return; }
            totalW += w;
            if (isMarked(r)) { markedW += w; earned += r.pct * w / 100; }
        });

        const weighted = [];
        if (markedW > 0) {
            weighted.push(`Weighted: ${r1(earned)} of ${r1(markedW)} marked (${r1(earned / markedW * 100)}%)`);
            const remaining = totalW - markedW;
            if (!missing && totalW > 99 && totalW < 101 && remaining > 0.5) {     // only when the weights add up to 100%
                const need = (PASS_MARK - earned) / remaining * 100;
                weighted.push(need <= 0 ? `${PASS_MARK}% already secured`
                    : need > 100 ? `${PASS_MARK}% out of reach (would need ${r1(need)}%)`
                    : `need ${r1(need)}% on the remaining ${r1(remaining)}% to reach ${PASS_MARK}%`);
            } else if (missing) weighted.push(`weights missing for ${missing}`);
        } else if (totalW > 0) weighted.push(marks.length && missing ? `weights missing for ${missing}` : 'Nothing weighted is marked yet');

        return { rows, marks, weightOf, weighted };
    }

    /* =====================================================================
     * CARDS: lookup helpers and custom order
     * ===================================================================== */
    const cardSid = a => { const m = (a.getAttribute('href') || '').match(/\/subject\/(\d+)/); return m ? +m[1] : 0; };
    const getContainer = () => document.querySelector('.moduleCardContainer');
    const getAllCards = c => [...c.querySelectorAll(':scope > a[href*="/subject/"]')];
    const isHidden = a => EXCLUDE.includes(cardSid(a)) || SETTINGS.hiddenCourses.includes(cardSid(a));
    const getCards = c => getAllCards(c).filter(a => !isHidden(a));
    const sigOf = cards => cards.map(cardSid).join(',');
    const hasRows = d => !!d && Object.keys(d.rows).length > 0;

    // Course ids shown on the dashboard (in their current order) that have results
    function gridSids() {
        const data = loadGrades();
        return [...document.querySelectorAll('#myAIE-grid > a')].map(c => +c.dataset.sid).filter(s => s && hasRows(data[s]));
    }

    const orderIdx = (order, sid) => { const i = order.indexOf(sid); return i < 0 ? 1e6 : i; };

    function sortByOrder(cards) {
        const order = loadOrder();
        return cards.map((a, i) => ({ a, i }))
            .sort((x, y) => (orderIdx(order, cardSid(x.a)) - orderIdx(order, cardSid(y.a))) || (x.i - y.i))
            .map(x => x.a);
    }

    function saveOrder(grid) {
        const sids = [...grid.children].map(c => +c.dataset.sid).filter(Boolean);
        const hidden = loadOrder().filter(s => !sids.includes(s));      // keep ids that are currently filtered out
        writeJSON(KEYS.order, [...sids, ...hidden]);
        syncSidebar();
    }

    // Plain course links only: not assessment links, and nothing inside a table
    const isCourseLink = a => /\/course\/\d+\/subject\/\d+\/?$/.test((a.getAttribute('href') || '').split('?')[0]) && !a.closest('table');

    // Reorders any OTHER list of course links on the page (e.g. a left-hand course list) to match the saved order
    function syncSidebar() {
        const order = loadOrder();
        if (!order.length) return;

        const links = [...document.querySelectorAll('a[href*="/subject/"]')]
            .filter(a => isCourseLink(a) && !a.closest('#myAIE-results') && !a.closest('.moduleCardContainer'));
        const courseLinksIn = el => [...el.querySelectorAll('a[href*="/subject/"]')].filter(isCourseLink);

        const groups = new Map();                                   // parent element -> its list items
        links.forEach(a => {
            let item = a;
            while (item.parentElement && courseLinksIn(item.parentElement).length === 1) item = item.parentElement;
            const parent = item.parentElement;
            if (!parent) return;
            if (!groups.has(parent)) groups.set(parent, []);
            if (!groups.get(parent).includes(item)) groups.get(parent).push(item);
        });

        const sidOf = el => { const a = (el.matches('a') && isCourseLink(el)) ? el : courseLinksIn(el)[0]; return a ? cardSid(a) : 0; };
        groups.forEach(items => {
            if (items.length < 2) return;
            const sorted = [...items].sort((x, y) => orderIdx(order, sidOf(x)) - orderIdx(order, sidOf(y)));
            if (sorted.every((el, i) => el === items[i])) return;
            const markers = items.map(el => { const m = document.createComment(''); el.before(m); return m; });   // keep each slot
            sorted.forEach((el, i) => markers[i].after(el));
            markers.forEach(m => m.remove());
        });
    }

    /* =====================================================================
     * TEMPLATES: the HTML inside each card
     * ===================================================================== */
    const BOX = 'width:100%;box-sizing:border-box;font-size:13px;margin-bottom:10px;padding:8px 10px;border-radius:8px;';
    const BOX_TODAY = BOX + `background:${rgb(P.teal, .12)};border:1px solid ${rgb(P.teal, .35)}`;
    const BOX_EMPTY = BOX + 'background:rgba(128,128,128,.10);border:1px solid rgba(128,128,128,.25)';
    const ROW = 'display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px;align-items:center;padding:3px 0;';
    const ELLIPSIS = 'min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;';

    function pill(result) {
        const base = 'display:inline-block;max-width:100%;box-sizing:border-box;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;vertical-align:middle;height:22px;line-height:22px;padding:0 8px;border-radius:10px;font-size:12px;font-weight:600;';
        const colour = result === 'Pass' ? `background:${rgb(P.green)};color:#fff`
            : result === 'Fail' ? `background:${rgb(P.red)};color:#fff`
            : 'background:rgba(173,181,189,.25);color:inherit';
        return `<span style="${base}${colour}">${esc(result)}</span>`;
    }

    const TYPE_LABELS = { bbb_class: 'Virtual', hybrid: 'Hybrid' };
    const typeOf = it => TYPE_LABELS[it.class_type] || 'Class';
    const timeRange = it => esc(it.class_from) + ' - ' + esc(it.class_to);
    const dayLabel = ymd => {
        const p = String(ymd || '').split('-');
        return p.length < 3 ? '' : new Date(+p[0], +p[1] - 1, +p[2]).toLocaleDateString(undefined, { weekday: 'short', day: 'numeric', month: 'short' });
    };

    function untilText(startSec, endSec) {
        const now = Date.now() / 1000;
        if (now >= startSec && now < endSec) return 'live now';
        const mins = Math.round((startSec - now) / 60);
        if (mins < 1) return 'starting now';
        if (mins < 60) return 'in ' + mins + ' min';
        const hours = Math.floor(mins / 60);
        if (hours < 24) return 'in ' + hours + 'h ' + (mins % 60) + 'm';
        const days = Math.floor(hours / 24);
        return 'in ' + days + ' day' + (days > 1 ? 's' : '');
    }

    function nextLine(s, skipIfToday) {
        const n = s && s.next;
        if (!n || (skipIfToday && n.class_date === dateKey(new Date()))) return '';
        return `<div style="opacity:.8;font-size:12px;padding-top:4px">Next: ${esc(dayLabel(n.class_date))} &middot; ${timeRange(n)} &middot; ${typeOf(n)}</div>`;
    }

    function upNextHtml(n) {
        const nowSec = Date.now() / 1000;
        const live = n.is_live || (nowSec >= n.class_start_dt && nowSec < n.class_end_dt);
        return `<div style="width:100%;box-sizing:border-box;margin-bottom:8px;padding:6px 10px;border-radius:8px;background:${rgb(P.teal)};color:#fff;font-size:12px;font-weight:700">${live ? 'LIVE NOW' : 'UP NEXT'} &middot; ${esc(dayLabel(n.class_date))} ${timeRange(n)} &middot; ${typeOf(n)} &middot; ${untilText(n.class_start_dt, n.class_end_dt)}</div>`;
    }

    function classState(it) {
        const label = it.canceled ? 'Cancelled' : it.is_live ? 'Live' : it.is_past ? 'Ended' : 'Upcoming';
        const chip = label === 'Live' ? `background:${rgb(P.green)};color:#fff;`
            : label === 'Cancelled' ? `background:${rgb(P.red)};color:#fff;`
            : 'background:rgba(173,181,189,.25);color:inherit;';
        return {
            label, chip,
            joinable: !it.canceled && !it.disable_join_button && (it.show_join_button || it.is_live),
            over: !!(it.is_past || it.canceled)
        };
    }

    function assessmentRow(it) {
        return `<div style="${ROW}"><span style="${ELLIPSIS}" title="${esc(it.name)}"><b>${timeRange(it)}</b> &middot; ${esc(shortName(it.name))} (${esc(it.ass_type)})</span><span>${pill(it.assessment_status || it.status || 'Pending')}</span></div>`;
    }

    function classRow(it) {
        const { label, chip, joinable, over } = classState(it);
        const btnBase = 'padding:4px 12px;border:none;border-radius:6px;font-size:12px;font-weight:600;white-space:nowrap;';
        const chipBase = 'display:inline-block;height:20px;line-height:20px;padding:0 8px;border-radius:10px;font-size:11px;font-weight:600;margin-left:6px;';
        const btn = over ? '' :
            `<button data-join="1" data-cid="${esc(it.id)}" ${joinable ? '' : 'disabled'} title="${joinable ? 'Join this class' : 'Not open yet'}" style="${btnBase}${joinable ? `background:${rgb(P.green)};color:#fff;cursor:pointer;` : 'background:rgba(173,181,189,.3);color:inherit;cursor:not-allowed;opacity:.7;'}">Join</button>`;
        return `<div style="${ROW}${over ? 'opacity:.6;' : ''}"><span style="min-width:0"><b>${timeRange(it)}</b> &middot; ${typeOf(it)}<span style="${chipBase}${chip}">${label}</span></span><span>${btn}</span></div>`;
    }

    function todayHtml(sid) {
        const s = schedule[sid];
        if (!s) return '';
        if (!s.items.length) {
            return `<div style="${BOX_EMPTY}"><b>Today</b> &middot; <span style="opacity:.75">No classes today</span>${nextLine(s, false)}</div>`;
        }
        let h = `<div style="${BOX_TODAY}"><div style="font-weight:700;margin-bottom:4px">Today</div>`;
        if (!s.items.some(it => it.category !== 'task')) h += '<div style="opacity:.75;padding:3px 0">No classes today</div>';
        s.items.forEach(it => { h += it.category === 'task' ? assessmentRow(it) : classRow(it); });
        return h + nextLine(s, true) + '</div>';
    }

    // The marks table. Adds this course's marks to allMarks for the overall average.
    function bodyHtml(sid, d, allMarks) {
        if (!d) return `<div style="font-size:13px;opacity:.7">${emptySids.has(sid) ? 'No assessments yet.' : 'Loading grades...'}</div>`;
        const { rows, marks, weightOf, weighted } = courseStats(sid, d);
        const { showPercent, showWeights } = SETTINGS;
        allMarks.push(...marks);
        const wLine = showPercent ? weighted.join(' &middot; ') : '';
        const columns = showPercent ? 'minmax(0,1fr) 52px 120px' : 'minmax(0,1fr) 120px';

        let h = `<div style="width:100%;font-size:13px"><div style="font-weight:700;margin-bottom:${wLine ? 2 : 6}px">${showPercent ? `Average ${fmtAvg(marks)} &middot; ` : ''}${marks.length}/${rows.length} marked</div>`;
        if (wLine) h += `<div style="font-size:12px;opacity:.8;margin-bottom:6px">${wLine}</div>`;
        rows.forEach(r => {
            const w = showWeights ? weightOf(r) : null;
            const score = !showPercent ? '' : `<span style="text-align:right;white-space:nowrap">${isScored(r) ? (isFuture(r) ? `<span title="Not counted: this assessment hasn't taken place yet" style="opacity:.5">${esc(r.pct)}%*</span>` : `<b>${esc(r.pct)}%</b>`) : '-'}</span>`;
            h += `<div style="display:grid;grid-template-columns:${columns};align-items:center;gap:8px;padding:4px 0;border-top:1px solid rgba(128,128,128,.25)">
                <span title="${esc(r.name)}" style="${ELLIPSIS}">${esc(shortName(r.name))}${w !== null ? ` <span style="opacity:.6">(${r1(w)}%)</span>` : ''}</span>
                ${score}
                <span style="text-align:right;min-width:0">${pill(r.result)}</span></div>`;
        });
        if (showPercent && rows.some(r => isScored(r) && isFuture(r))) h += `<div style="font-size:11px;opacity:.7;padding-top:4px">* Not counted: this assessment hasn't taken place yet.</div>`;
        return h + '</div>';
    }

    /* =====================================================================
     * PDF: subject picker popup + unofficial summary (one page per course)
     * ===================================================================== */
    const PDF = { L: 15, R: 195, X1: 110, X2: 135, X3: 160, LINE: [210, 214, 220] };   // page margins and table column dividers (mm)
    const cleanText = s => String(s || '').replace(/\s+/g, ' ').trim();
    // jsPDF's built-in fonts only cover Latin-1: swap common punctuation for plain characters and replace the rest
    const pdfText = s => cleanText(s).replace(/[\u2010-\u2015\u2212]/g, '-').replace(/[\u2018\u2019\u201A]/g, "'").replace(/[\u201C\u201D\u201E]/g, '"')
        .replace(/\u2026/g, '...').replace(/[^\x20-\x7E\u00A1-\u00FF]/g, '?');

    function closeModal() {
        document.getElementById('myAIE-modal')?.remove();
        document.getElementById('myAIE-modal-backdrop')?.remove();
        document.body.classList.remove('modal-open');
        if (modalKeyHandler) { document.removeEventListener('keydown', modalKeyHandler); modalKeyHandler = null; }
    }

    // A popup built from the site's own Bootstrap modal classes so it looks like the site's other popups.
    // Anything inside with data-cancel closes it; so do Esc and a click outside.
    function showModal({ title, icon, body, width = 480 }) {
        closeModal();
        const backdrop = document.createElement('div');
        backdrop.id = 'myAIE-modal-backdrop';
        backdrop.className = 'modal-backdrop fade show';
        backdrop.style.zIndex = '2147483645';

        const modal = document.createElement('div');
        modal.id = 'myAIE-modal';
        modal.className = 'topic-add-modal modal fade show zindexadd';
        modal.setAttribute('role', 'dialog');
        modal.setAttribute('aria-label', title);
        modal.style.cssText = 'display:block;z-index:2147483646;overflow-y:auto;';
        modal.innerHTML = `<div class="modal-dialog modal-dialog-centered" role="document" style="max-width:${width}px">
            <div class="modal-content">
                <div class="modal-header modal-header-custom">
                    <h6 class="modal-title"><i class="fal ${icon}"></i> ${esc(title)}</h6>
                    <button type="button" class="close" data-cancel="1" aria-label="Close"><span aria-hidden="true">&times;</span></button>
                </div>
                <div class="modal-body class-launch-modal">${body}</div>
            </div></div>`;
        document.body.append(backdrop, modal);
        document.body.classList.add('modal-open');

        modalKeyHandler = e => { if (e.key === 'Escape') closeModal(); };
        document.addEventListener('keydown', modalKeyHandler);
        modal.addEventListener('click', e => { if (e.target === modal) closeModal(); });
        modal.querySelectorAll('[data-cancel]').forEach(b => { b.onclick = closeModal; });
        return modal;
    }

    function openPdfPicker() {
        const data = loadGrades();
        const sids = gridSids();
        if (!sids.length) { alert('No results are loaded yet.'); return; }

        const border = rgb(P.border);
        const checkbox = 'width:16px;height:16px;flex:none;margin:0;cursor:pointer;accent-color:' + rgb(P.blue);
        const cell = 'display:flex;align-items:center;gap:14px;flex:1 0 0;min-width:0;border-right:1px solid ' + border;
        const avgCell = 'display:flex;align-items:center;justify-content:center;width:25%;padding:0 12px;';
        const dlIcon = '<i class="fal fa-download" style="margin-left: 8px;"></i>';

        const rowsHtml = sids.map((s, i) => {
            const d = data[s];
            const code = d.code || cleanText(d.courseName);
            const avg = fmtAvg(courseStats(s, d).marks, '-');
            return `<label style="display:flex;width:100%;min-height:52px;margin:0;align-items:stretch;cursor:pointer;background:#fff;${i < sids.length - 1 ? 'border-bottom:1px solid ' + border + ';' : ''}">
                <span style="${cell};padding:12px 0 12px 24px">
                    <input type="checkbox" data-sid="${esc(s)}" checked style="${checkbox}">
                    <span style="color:${rgb(P.blue)};font-size:14px;font-weight:700">${esc(code)}</span>
                </span>
                <span style="${avgCell}font-size:14px;color:${rgb(P.text)}">${esc(avg)}</span></label>`;
        }).join('');

        const modal = showModal({
            title: 'Download PDF', icon: 'fa-file-pdf', width: 480,
            body: `<div style="border:1px solid ${border};border-radius:10px;overflow:hidden;background:#fff">
                    <label style="display:flex;width:100%;height:56px;margin:0;align-items:stretch;cursor:pointer;border-bottom:1px solid ${border};font-size:14px;font-weight:700;color:${rgb(P.text)}">
                        <span style="${cell};padding:0 0 0 24px">
                            <input type="checkbox" id="myAIE-pick-all" style="${checkbox}">
                            <span>Course</span>
                        </span>
                        <span style="${avgCell}">Average</span>
                    </label>
                    <div style="max-height:46vh;overflow-y:auto">${rowsHtml}</div>
                </div>
                <div style="display:flex;justify-content:flex-end;gap:10px;margin-top:20px">
                    <button type="button" class="btn btn-secondary" data-cancel="1">Cancel</button>
                    <button type="button" class="btn btn-primary" data-go="1">Download${dlIcon}</button>
                </div>`
        });

        const boxes = () => [...modal.querySelectorAll('input[data-sid]')];
        const allBox = modal.querySelector('#myAIE-pick-all');
        const goBtn = modal.querySelector('[data-go]');
        const sync = () => {
            const all = boxes(), n = all.filter(b => b.checked).length;
            goBtn.disabled = !n;
            goBtn.innerHTML = (n ? `Download (${n})` : 'Download') + dlIcon;
            allBox.checked = n === all.length;
            allBox.indeterminate = n > 0 && n < all.length;
        };
        allBox.addEventListener('change', () => { boxes().forEach(b => { b.checked = allBox.checked; }); sync(); });
        boxes().forEach(b => b.addEventListener('change', sync));
        goBtn.onclick = () => {
            const picked = boxes().filter(b => b.checked).map(b => +b.dataset.sid);
            closeModal();
            if (picked.length) downloadPdf(picked);
        };
        sync();
    }

    function loadJsPdf() {
        return new Promise((resolve, reject) => {
            const ready = () => window.jspdf && window.jspdf.jsPDF;
            if (ready()) return resolve(ready());
            const s = document.createElement('script');
            s.src = JSPDF_URL;
            s.onload = () => ready() ? resolve(ready()) : reject(new Error('the PDF library loaded but did not start'));
            s.onerror = () => reject(new Error('could not download the PDF library (blocked or offline)'));
            document.head.appendChild(s);
            setTimeout(() => reject(new Error('timed out loading the PDF library')), 15000);
        });
    }

    async function downloadPdf(selected) {
        const btn = document.getElementById('myAIE-pdf');
        const label = btn ? btn.innerHTML : '';
        if (btn) { btn.textContent = 'Creating PDF...'; btn.disabled = true; }
        try {
            buildPdf(await loadJsPdf(), selected);
        } catch (e) {
            console.error('[myAIE] PDF failed', e);
            alert('PDF failed: ' + (e && e.message ? e.message : e));
        }
        const after = document.getElementById('myAIE-pdf');
        if (after) { after.innerHTML = label || 'Summary'; after.disabled = false; }
    }

    function buildPdf(lib, selected) {
        const data = loadGrades();
        const sids = ((selected && selected.length) ? selected : gridSids()).filter(s => hasRows(data[s]));
        if (!sids.length) { alert('No results are loaded yet.'); return; }

        const doc = new lib({ unit: 'mm', format: 'a4' });
        const issued = issuedDate();
        sids.forEach((sid, i) => {
            if (i) doc.addPage();
            drawCoursePage(doc, sid, data[sid], i, sids.length, issued);
        });
        doc.save('myAIE-results-' + dateKey(new Date()) + '.pdf');
    }

    const issuedDate = () => new Date().toLocaleDateString('en-ZA', { day: 'numeric', month: 'long', year: 'numeric' });

    function pdfTools(doc) {
        const font = (style, size, color) => { doc.setFont('helvetica', style); doc.setFontSize(size); doc.setTextColor(...color); };
        const keyValue = (label, value, x, y) => {
            font('bold', 10, P.navy);
            doc.text(label, x, y);
            const labelWidth = doc.getTextWidth(label + ' ');
            font('normal', 10, [30, 30, 30]);
            doc.text(String(value), x + labelWidth, y);
        };
        return { font, keyValue };
    }

    function pdfFooter(doc, label) {
        doc.setFont('helvetica', 'normal'); doc.setFontSize(9); doc.setTextColor(...P.grey);
        doc.text(label, 105, 283, { align: 'center' });
        doc.setDrawColor(...P.navy); doc.setLineWidth(0.4);
        doc.line(30, 288, 180, 288);
    }

    function drawCoursePage(doc, sid, d, idx, total, issued) {
        const { L, R, X1, X2, X3, LINE } = PDF, W = R - L;
        const { rows, marks, weightOf, weighted } = courseStats(sid, d);
        const code = pdfText(d.code);

        const { font, keyValue } = pdfTools(doc);

        // Title and disclaimer
        font('bold', 20, P.navy);
        doc.text('Results Summary', L, 28);
        font('normal', 13, P.navy);
        doc.text(pdfText(d.courseName || code), L, 36);
        font('normal', 8.5, P.grey);
        doc.text(doc.splitTextToSize('Unofficial summary generated from your myAIE results by a personal script. It is not a Statement of Results.', W), L, 42);

        // Info box
        doc.setFillColor(246, 246, 250);
        doc.roundedRect(L, 50, W, 22, 3, 3, 'F');
        keyValue('Course code:', code || '-', L + 6, 58);
        keyValue('Date generated:', issued, L + 6, 66);
        keyValue('Average:', fmtAvg(marks) + ' (unweighted)', L + 100, 58);
        keyValue('Marked:', marks.length + ' of ' + rows.length, L + 100, 66);

        let y = 80;
        if (weighted.length) {
            font('normal', 9, P.navy);
            const lines = doc.splitTextToSize(weighted.join(' | '), W);
            doc.text(lines, L, y);
            y += lines.length * 4.4 + 4;
        }

        // Table: measure the rows first so the outline fits
        font('bold', 10, P.navy);
        const items = rows.map(r => {
            const lines = doc.splitTextToSize(pdfText(r.name), X1 - L - 12);
            return { r, lines, h: Math.max(15, lines.length * 4.6 + 8) };
        });
        const headH = 11, top = y;
        const tableH = headH + items.reduce((sum, it) => sum + it.h, 0);
        const mid12 = (X1 + X2) / 2, mid23 = (X2 + X3) / 2, mid3R = (X3 + R) / 2;

        doc.setDrawColor(...LINE); doc.setLineWidth(0.25);
        doc.roundedRect(L, top, W, tableH, 2, 2, 'S');
        [X1, X2, X3].forEach(x => doc.line(x, top, x, top + tableH));

        font('bold', 10, [0, 0, 0]);
        doc.text('Assessments', L + 6, top + 7);
        doc.text('Weight', mid12, top + 7, { align: 'center' });
        doc.text('Grade', mid23, top + 7, { align: 'center' });
        doc.text('Result', mid3R, top + 7, { align: 'center' });
        doc.line(L, top + headH, R, top + headH);

        let rowY = top + headH;
        items.forEach((it, i) => {
            const { r, lines, h } = it, mid = rowY + h / 2;

            font('bold', 10, P.navy);
            doc.text(lines, L + 6, rowY + 6.5);
            font('normal', 8, P.grey);
            doc.text(pdfText((r.type || '') + ' ' + code), L + 6, rowY + 6.5 + (lines.length - 1) * 4.6 + 4.6);

            const w = weightOf(r);
            font('normal', 10, P.text);
            doc.text(w !== null ? r1(w) + '%' : '-', mid12, mid + 1.2, { align: 'center' });
            doc.text(isScored(r) ? r.pct + '%' + (isFuture(r) ? ' *' : '') : '-', mid23, mid + 1.2, { align: 'center' });

            // Result pill
            const label = String(r.result || 'Pending');
            doc.setFont('helvetica', 'bold'); doc.setFontSize(8);
            const pillW = Math.max(15, doc.getTextWidth(label) + 7);
            const [fill, ink] = label === 'Pass' ? [P.green, [255, 255, 255]] : label === 'Fail' ? [P.red, [255, 255, 255]] : [[236, 237, 240], P.text];
            doc.setFillColor(...fill); doc.setTextColor(...ink);
            doc.roundedRect(mid3R - pillW / 2, mid - 3, pillW, 6, 3, 3, 'F');
            doc.text(label, mid3R, mid + 1.1, { align: 'center' });

            rowY += h;
            if (i < items.length - 1) { doc.setDrawColor(...LINE); doc.line(L, rowY, R, rowY); }
        });

        if (rows.some(r => isScored(r) && isFuture(r))) {
            font('normal', 8, P.grey);
            doc.text('* Not counted in the average: the assessment has not taken place yet.', L, top + tableH + 6);
        }
        pdfFooter(doc, (idx + 1) + '/' + total);
    }

    /* =====================================================================
     * EXAM DATES PDF
     * ===================================================================== */
    const isExam = it => it.category === 'task' && (/exam/i.test(it.ass_type || '') || /exam/i.test(it.name || ''));

    // A fresh lookup of every upcoming exam across the given courses
    async function collectExams(sids) {
        const found = new Map();                                    // assessment id -> exam
        const nowSec = Date.now() / 1000;
        const today = new Date(); today.setHours(0, 0, 0, 0);
        await Promise.all(sids.map(async sid => {
            const seen = new Set();
            for (let page = 1; page <= MAX_PAGES; page++) {
                const j = await postSchedule(sid, { page, listType: 'upcoming', from: today.toISOString(), to: WEIGHT_RANGE.to });
                if (!j) break;
                let added = 0;
                scheduleItems(j).forEach(it => {
                    const key = (it.category || '') + ':' + (it.id ?? it.assessment_id);
                    if (seen.has(key)) return;
                    seen.add(key); added++;
                    if (!isExam(it) || !it.open_date_time || !(it.close_date_time > nowSec)) return;
                    const own = (SETTINGS.weights[sid] || {})[it.assessment_id];     // your own weighting wins
                    found.set(it.assessment_id, {
                        name: pdfText(it.name), code: pdfText(it.code), course: pdfText(it.subjectName), type: pdfText(it.ass_type) || 'Exam',
                        opens: it.open_date_time, closes: it.close_date_time, from: it.class_from, to: it.class_to,
                        weight: own !== undefined ? own : (it.ass_weighting != null ? parseFloat(it.ass_weighting) : null),
                        minutes: it.timeLimitActive ? (it.timeHour || 0) * 60 + (it.timeMin || 0) : Math.round((it.close_date_time - it.open_date_time) / 60)
                    });
                });
                if (!added) break;
            }
        }));
        return [...found.values()].sort((a, b) => a.opens - b.opens);
    }

    const fmtDuration = m => !m || m < 1 ? '' : m >= 60 ? Math.floor(m / 60) + 'h' + (m % 60 ? ' ' + (m % 60) + 'm' : '') : m + 'm';

    function examWhen(e) {
        const d = new Date(e.opens * 1000);
        const day0 = x => { const c = new Date(x); c.setHours(0, 0, 0, 0); return c.getTime(); };
        const diff = Math.round((day0(d) - day0(Date.now())) / 86400000);
        const clock = ts => cleanText(new Date(ts * 1000).toLocaleTimeString('en-US', { hour: 'numeric', minute: '2-digit', hour12: true }));
        return {
            date: cleanText(d.toLocaleDateString('en-ZA', { weekday: 'short', day: 'numeric', month: 'short', year: 'numeric' })),
            rel: diff <= 0 ? 'today' : diff === 1 ? 'tomorrow' : 'in ' + diff + ' days',
            time: (e.from && e.to) ? e.from + ' - ' + e.to : clock(e.opens) + ' - ' + clock(e.closes)
        };
    }

    function buildExamPdf(lib, exams) {
        const { L, R, LINE } = PDF, W = R - L;
        const X1 = 70, X2 = 120, HEAD_H = 11, BOTTOM = 275;       // column dividers, header row height, last usable y (mm)
        const doc = new lib({ unit: 'mm', format: 'a4' });
        const { font, keyValue } = pdfTools(doc);
        const courses = new Set(exams.map(e => e.code || e.course));
        const first = examWhen(exams[0]);

        // Title block (first page only)
        font('bold', 20, P.navy);
        doc.text('Upcoming Exams', L, 28);
        font('normal', 13, P.navy);
        doc.text(exams.length + (exams.length === 1 ? ' exam' : ' exams') + ' across ' + courses.size + (courses.size === 1 ? ' course' : ' courses'), L, 36);
        font('normal', 8.5, P.grey);
        doc.text(doc.splitTextToSize('Unofficial summary generated from your myAIE schedule by a personal script. Always confirm dates, times and venues on myAIE.', W), L, 42);
        doc.setFillColor(246, 246, 250);
        doc.roundedRect(L, 50, W, 22, 3, 3, 'F');
        keyValue('Date generated:', issuedDate(), L + 6, 58);
        keyValue('Exams listed:', exams.length, L + 6, 66);
        keyValue('Next exam:', first.date, L + 100, 58);
        keyValue('Course:', exams[0].code || exams[0].course, L + 100, 66);

        // Measure the rows, then split them across pages
        font('bold', 10, P.navy);
        const items = exams.map(e => {
            const lines = doc.splitTextToSize(e.name, R - X2 - 12);
            return { e, lines, h: Math.max(17, lines.length * 4.6 + 10) };
        });
        const pages = [];
        let cur = [], used = 0, cap = BOTTOM - 80 - HEAD_H;
        items.forEach(it => {
            if (cur.length && used + it.h > cap) { pages.push(cur); cur = []; used = 0; cap = BOTTOM - 25 - HEAD_H; }
            cur.push(it); used += it.h;
        });
        pages.push(cur);

        pages.forEach((rows, pi) => {
            if (pi) doc.addPage();
            const top = pi === 0 ? 80 : 25;
            const tableH = HEAD_H + rows.reduce((sum, it) => sum + it.h, 0);

            doc.setDrawColor(...LINE); doc.setLineWidth(0.25);
            doc.roundedRect(L, top, W, tableH, 2, 2, 'S');
            [X1, X2].forEach(x => doc.line(x, top, x, top + tableH));
            font('bold', 10, [0, 0, 0]);
            doc.text('Date', L + 6, top + 7);
            doc.text('Time', X1 + 6, top + 7);
            doc.text('Exam', X2 + 6, top + 7);
            doc.line(L, top + HEAD_H, R, top + HEAD_H);

            let y = top + HEAD_H;
            rows.forEach((it, i) => {
                const { e, lines, h } = it, when = examWhen(e), dur = fmtDuration(e.minutes);
                font('bold', 10, P.navy);   doc.text(when.date, L + 6, y + 7);
                font('normal', 8, P.grey);  doc.text(when.rel, L + 6, y + 12);
                font('normal', 10, P.text); doc.text(when.time, X1 + 6, y + 7);
                if (dur) { font('normal', 8, P.grey); doc.text(dur, X1 + 6, y + 12); }
                font('bold', 10, P.navy);   doc.text(lines, X2 + 6, y + 7);
                font('normal', 8, P.grey);
                doc.text(pdfText([e.code, e.type, e.weight != null ? r1(e.weight) + '% weighting' : ''].filter(Boolean).join(' | ')),
                    X2 + 6, y + 7 + (lines.length - 1) * 4.6 + 4.6);
                y += h;
                if (i < rows.length - 1) { doc.setDrawColor(...LINE); doc.line(L, y, R, y); }
            });
            pdfFooter(doc, (pi + 1) + '/' + pages.length);
        });
        doc.save('myAIE-exam-dates-' + dateKey(new Date()) + '.pdf');
    }

    async function downloadExamPdf() {
        const btn = document.getElementById('myAIE-exams');
        const label = btn ? btn.innerHTML : '';
        if (btn) { btn.textContent = 'Finding exams...'; btn.disabled = true; }
        try {
            if (!TOKEN) TOKEN = tokenFromStorage();
            if (!TOKEN) throw new Error('you are not logged in yet. Refresh the page and try again.');
            const sids = [...document.querySelectorAll('#myAIE-grid > a')].map(c => +c.dataset.sid).filter(Boolean);
            const [lib, exams] = await Promise.all([loadJsPdf(), collectExams(sids)]);
            if (!exams.length) alert('No upcoming exams were found in your schedule.');
            else buildExamPdf(lib, exams);
        } catch (e) {
            console.error('[myAIE] Exam PDF failed', e);
            alert('Exam PDF failed: ' + (e && e.message ? e.message : e));
        }
        const after = document.getElementById('myAIE-exams');
        if (after) { after.innerHTML = label || 'Exam dates'; after.disabled = false; }
    }

    /* =====================================================================
     * SETTINGS PAGE: adds the dashboard options to the site's own /settings page,
     * using the same classes as the existing "Calendar" setting so it looks native
     * ===================================================================== */
    const TOGGLES = [
        ['showPercent', 'Percentages', 'Marks, averages and the weighted line'],
        ['showWeights', 'Weightings', 'The weighting (for example 15%) next to each assessment'],
        ['showProgress', 'Course progress', 'The progress bar from the original course card'],
        ['showToday', "Today's classes and next class", 'The box with class times, Join buttons and the next class'],
        ['showUpNext', 'Up next banner', 'The banner and highlight on the card with your next class']
    ];

    function applySettings(next) {
        SETTINGS = normalizeSettings(next);
        writeJSON(KEYS.settings, SETTINGS);
        render();                                                    // does nothing unless the courses page is open
    }

    // The settings page has no course cards, so the course list is remembered from the courses page
    function rememberCourses(allCards) {
        const list = allCards.map(a => ({ sid: cardSid(a), title: cleanText(a.getAttribute('title')) })).filter(c => c.sid);
        if (JSON.stringify(list) !== JSON.stringify(readJSON(KEYS.courses, []))) writeJSON(KEYS.courses, list);
    }

    function knownCourses() {
        const data = loadGrades();
        return readJSON(KEYS.courses, []).filter(c => c.sid && !EXCLUDE.includes(c.sid))
            .map(c => ({ ...c, code: (data[c.sid] && data[c.sid].code) || '' }));
    }

    // ---- HTML builders (same markup as the site's own setting rows) ----
    const showHideSelect = (attr, value, on) =>
        `<select class="form-control selectcontrol" ${attr}="${esc(value)}" style="min-width:110px"><option value="1"${on ? ' selected' : ''}>Show</option><option value="0"${on ? '' : ' selected'}>Hide</option></select>`;

    // label and hint must already be escaped
    const settingRow = (label, hint, control) =>
        `<div class="form-item d-flex align-items-center"><div style="min-width:0"><div class="secondary-label">${label}</div>${hint ? `<small style="color:${rgb(P.grey)}">${hint}</small>` : ''}</div><div class="form-item-control ml-auto">${control}</div></div>`;

    function weightEditorHtml(sid, draft, data) {
        const fetched = (WEIGHTS[sid] && WEIGHTS[sid].map) || {};
        const own = draft.weights[sid] || {};
        return Object.values(data[sid].rows).map(r => settingRow(esc(shortName(r.name)), esc(r.type),
            `<input type="number" class="form-control" min="0" max="100" step="0.5" data-aid="${esc(r.id)}" value="${esc(own[r.id] ?? '')}" placeholder="${esc(fetched[r.id] ?? '-')}" style="width:100px;text-align:right">`)).join('');
    }

    function weightTotalHtml(sid, draft, data) {
        const fetched = (WEIGHTS[sid] && WEIGHTS[sid].map) || {};
        const own = draft.weights[sid] || {};
        const total = Object.values(data[sid].rows).reduce((sum, r) => sum + (own[r.id] ?? fetched[r.id] ?? 0), 0);
        return `Total: <b>${r1(total)}%</b>` + (Math.abs(total - 100) < 0.01 ? '' : ' <span style="color:#b9770e">(should add up to 100%)</span>');
    }

    const moduleLabel = c => c.code ? c.code + ' - ' + c.title : c.title;

    // Everything that can be edited for ONE module: is it shown, and what are its weightings
    function moduleEditorHtml(sid, draft, data) {
        const visibility = settingRow('Show this module', 'Hide it from the dashboard, the overall average and the PDFs',
            showHideSelect('data-course', sid, !draft.hiddenCourses.includes(sid)));
        const weights = hasRows(data[sid])
            ? settingRow('Your own weightings', 'Type a weighting for an assessment. Leave it empty to use the one from myAIE (shown greyed out).', '')
                + weightEditorHtml(sid, draft, data)
                + settingRow('<span id="myAIE-wtotal"></span>', '', '<a href="#" id="myAIE-wreset">Use myAIE\'s weightings</a>')
            : settingRow('No assessments loaded yet', 'Open My Courses once so the marks can be loaded.', '');
        return `<div class="form-item"><div class="item-label">Dashboard</div>${visibility}</div>
            <div class="form-item"><div class="item-label">Weightings</div>${weights}</div>`;
    }

    function settingsFormHtml(draft, courses, data, wrapClass, saveClass) {
        const display = TOGGLES.map(([key, label, hint]) => settingRow(esc(label), esc(hint), showHideSelect('data-toggle', key, draft[key]))).join('');
        const modules = courses.length
            ? settingRow('Choose a module', 'Pick the module you want to edit', `<select class="form-control selectcontrol" id="myAIE-msel">${courses.map(c => `<option value="${esc(c.sid)}">${esc(moduleLabel(c))}</option>`).join('')}</select>`)
            : settingRow('No modules yet', 'Open My Courses once so the module list can be loaded.', '');

        return `<div class="settings-title" style="margin-top:32px">Course dashboard</div>
            <form id="myAIE-settings-form"><div class="${esc(wrapClass)}">
                <div class="form-item"><div class="item-label">Display</div>${display}</div>
                <div class="form-item"><div class="item-label">Module</div>${modules}</div>
                <div id="myAIE-mbox"></div>
                <div class="form-item"><div class="item-label">Reset</div>${settingRow('Restore defaults', 'Clears every dashboard setting, hidden module and your own weightings', '<a href="#" data-reset="1">Reset all</a>')}</div>
                <div class="form-item save-setting"><div class="text-md-right d-flex justify-content-center justify-content-md-end align-items-center">
                    <span id="myAIE-saved" class="mr-3" style="color:${rgb(P.green)};font-weight:600"></span>
                    <button title="Save" type="submit" class="${esc(saveClass)}">Save</button>
                </div></div>
            </div></form>`;
    }

    // Adds the section to /settings once the page has rendered (and again if the site redraws it)
    function injectSettingsPage() {
        if (!location.pathname.startsWith('/settings')) return;
        const card = document.querySelector('.settings-card');
        if (!card || document.getElementById('myAIE-settings')) return;

        const siteWrap = card.querySelector('form > div');               // copy the site's own (generated) class names
        const siteSave = card.querySelector('.save-setting button');
        const data = loadGrades();
        const draft = JSON.parse(JSON.stringify(SETTINGS));              // edited freely, only applied on Save

        const section = document.createElement('div');
        section.id = 'myAIE-settings';
        section.innerHTML = settingsFormHtml(draft, knownCourses(), data, (siteWrap && siteWrap.className) || '', (siteSave && siteSave.className) || 'btn btn-primary');
        card.appendChild(section);

        section.querySelectorAll('select[data-toggle]').forEach(el => el.addEventListener('change', () => { draft[el.dataset.toggle] = el.value === '1'; }));

        // The module menu: shows the editor for the chosen module. Edits to every module are kept in `draft` until Save.
        const msel = section.querySelector('#myAIE-msel'), mbox = section.querySelector('#myAIE-mbox');
        const showModule = sid => {
            mbox.innerHTML = moduleEditorHtml(sid, draft, data);
            mbox.querySelector('select[data-course]').addEventListener('change', e => {
                draft.hiddenCourses = draft.hiddenCourses.filter(s => s !== sid);
                if (e.target.value === '0') draft.hiddenCourses.push(sid);
            });
            if (!hasRows(data[sid])) return;

            const updateTotal = () => { mbox.querySelector('#myAIE-wtotal').innerHTML = weightTotalHtml(sid, draft, data); };
            mbox.querySelectorAll('input[data-aid]').forEach(inp => inp.addEventListener('input', () => {
                const v = parseFloat(inp.value);
                const mine = draft.weights[sid] = draft.weights[sid] || {};
                if (inp.value === '' || isNaN(v)) delete mine[inp.dataset.aid]; else mine[inp.dataset.aid] = Math.min(100, Math.max(0, v));
                updateTotal();
            }));
            mbox.querySelector('#myAIE-wreset').onclick = e => { e.preventDefault(); delete draft.weights[sid]; showModule(sid); };
            updateTotal();
        };
        if (msel) { msel.addEventListener('change', () => showModule(+msel.value)); showModule(+msel.value); }

        section.querySelector('form').addEventListener('submit', e => {
            e.preventDefault();
            e.stopPropagation();                                         // the site's own form handler must not see this
            Object.keys(draft.weights).forEach(k => { if (!Object.keys(draft.weights[k]).length) delete draft.weights[k]; });
            applySettings(draft);
            const note = section.querySelector('#myAIE-saved');
            note.textContent = 'Saved';
            setTimeout(() => { note.textContent = ''; }, 2500);
        });
        section.querySelector('[data-reset]').onclick = e => {
            e.preventDefault();
            if (!confirm('Reset all dashboard settings (display options, hidden modules and your own weightings) to the defaults?')) return;
            applySettings({});
            section.remove();
            injectSettingsPage();
        };
    }

    /* =====================================================================
     * RENDER: replaces the course cards with result cards
     * ===================================================================== */
    const CSS = [
        '#myAIE-grid{display:grid!important;grid-template-columns:repeat(2,minmax(0,1fr))!important;gap:16px!important;}',
        '#myAIE-grid>a{width:auto!important;max-width:none!important;min-width:0!important;margin:0!important;}',
        '@media (max-width:900px){#myAIE-grid{grid-template-columns:1fr!important;}}',
        // iOS-style wiggle while a card is being dragged
        '@keyframes myaieJiggle{0%{transform:rotate(-0.5deg) translate(0.5px,0);}50%{transform:rotate(0.5deg) translate(-0.5px,0.5px);}100%{transform:rotate(-0.5deg) translate(0.5px,0);}}',
        '#myAIE-grid.myaie-jiggle>a:not(.myaie-dragged){animation:myaieJiggle .22s ease-in-out infinite;}',
        '#myAIE-grid.myaie-jiggle>a:nth-child(even):not(.myaie-dragged){animation-duration:.27s;animation-delay:-.1s;}',
        '#myAIE-grid.myaie-jiggle>a.myaie-dragged{transform:scale(1.03);}',
        '@media (prefers-reduced-motion:reduce){#myAIE-grid.myaie-jiggle>a{animation:none!important;}}'
    ].join('');

    function ensureStyles() {
        if (document.getElementById('myAIE-style')) return;
        const style = document.createElement('style');
        style.id = 'myAIE-style';
        style.textContent = CSS;
        (document.head || document.documentElement).appendChild(style);
    }

    function renderSoon() {
        clearTimeout(renderTimer);
        renderTimer = setTimeout(() => { if (document.getElementById('myAIE-results')) render(); }, 250);
    }

    // ---------- drag and drop ----------
    const setMove = e => { try { e.dataTransfer.dropEffect = 'move'; } catch (err) {} };

    // Moves dragEl next to target and slides the cards that shifted into place
    function swapCards(grid, dragEl, target) {
        const kids = [...grid.children];
        const before = new Map(kids.map(k => [k, k.getBoundingClientRect()]));
        if (kids.indexOf(dragEl) < kids.indexOf(target)) target.after(dragEl); else target.before(dragEl);
        swapUntil = Date.now() + SWAP_MS + 40;

        kids.forEach(k => {
            if (k === dragEl) return;                                // the card in your hand follows the cursor
            const was = before.get(k), now = k.getBoundingClientRect();
            const dx = was.left - now.left, dy = was.top - now.top;
            if (!dx && !dy) return;
            try {
                k.animate(
                    [{ transform: `translate(${dx}px, ${dy}px)` }, { transform: 'translate(0px, 0px)' }],
                    { duration: SWAP_MS, easing: 'cubic-bezier(.2,.8,.2,1)', composite: 'add' }
                );
            } catch (err) {}
        });
    }

    function enableDrag(card, grid, sid) {
        card.draggable = true;
        card.addEventListener('dragstart', e => {
            dragging = true;
            card.__drag = true;
            try { e.dataTransfer.effectAllowed = 'move'; e.dataTransfer.setData('text/plain', String(sid)); } catch (err) {}
            setTimeout(() => {                                       // after the drag image is captured
                card.style.opacity = '0.4';
                card.classList.add('myaie-dragged');
                grid.classList.add('myaie-jiggle');
            }, 0);
        });
        card.addEventListener('dragend', () => {
            card.style.opacity = '';
            card.classList.remove('myaie-dragged');
            grid.classList.remove('myaie-jiggle');
            card.__drag = false;
            dragging = false;
            saveOrder(grid);                                         // keeps whatever order is on screen
            if (SORT !== 'custom') { SORT = 'custom'; writeJSON(KEYS.sort, SORT); setTimeout(render, 0); }
        });
        card.addEventListener('dragover', e => {
            const dragEl = [...grid.children].find(k => k.__drag);
            if (!dragEl || dragEl === card) return;
            e.preventDefault();
            setMove(e);
            if (Date.now() < swapUntil) return;                      // let the slide finish before the next swap
            swapCards(grid, dragEl, card);
        });
    }

    // ---------- sorting ----------
    const courseTitle = a => cleanText(a.getAttribute('title'));
    const isExamRow = r => /exam/i.test(r.type || '') || /exam/i.test(r.name || '');

    // Average of the marks that count, or null if there are none
    function courseAvg(sid, data) {
        if (!hasRows(data[sid])) return null;
        const marks = courseStats(sid, data[sid]).marks;
        return marks.length ? mean(marks) : null;
    }

    // Start time (seconds) of the soonest exam that hasn't finished yet, or null
    function nextExamAt(sid, data) {
        if (!hasRows(data[sid])) return null;
        const nowSec = Date.now() / 1000;
        const times = Object.values(data[sid].rows).filter(r => isExamRow(r) && r.opens && (r.closes || r.opens) > nowSec).map(r => r.opens);
        return times.length ? Math.min(...times) : null;
    }

    // Orders the cards for the chosen sort mode. Ties, and courses with nothing to compare, keep your own order.
    function sortCards(cards, data) {
        const custom = sortByOrder(cards);
        if (SORT === 'custom') return custom;
        const rank = new Map(custom.map((a, i) => [a, i]));
        const byKey = (key, dir) => [...cards].sort((x, y) => {
            const kx = key(x), ky = key(y);
            if (kx === null || ky === null) return kx === ky ? rank.get(x) - rank.get(y) : (kx === null ? 1 : -1);   // nothing to compare goes last
            return dir * (kx < ky ? -1 : kx > ky ? 1 : 0) || rank.get(x) - rank.get(y);
        });
        if (SORT === 'alpha' || SORT === 'alphaDesc') {
            const dir = SORT === 'alpha' ? 1 : -1;
            return [...cards].sort((x, y) => dir * courseTitle(x).localeCompare(courseTitle(y), undefined, { sensitivity: 'base', numeric: true }) || rank.get(x) - rank.get(y));
        }
        if (SORT === 'avgDesc') return byKey(a => courseAvg(cardSid(a), data), -1);
        if (SORT === 'avgAsc') return byKey(a => courseAvg(cardSid(a), data), 1);
        if (SORT === 'exams') return byKey(a => nextExamAt(cardSid(a), data), 1);
        return custom;
    }

    // Shown on every card while sorting by exams, so the order makes sense
    function examLineHtml(sid, data) {
        if (SORT !== 'exams') return '';
        const at = nextExamAt(sid, data);
        if (at === null) return `<div style="${BOX_EMPTY}"><b>Next exam</b> &middot; <span style="opacity:.75">none scheduled</span></div>`;
        const when = examWhen({ opens: at, closes: at });
        return `<div style="${BOX_TODAY}"><b>Next exam</b> &middot; ${esc(when.date)} &middot; ${esc(when.time.split(' - ')[0])} <span style="opacity:.75">(${esc(when.rel)})</span></div>`;
    }

    function setSort(mode) {
        SORT = sanitizeSort(mode);
        writeJSON(KEYS.sort, SORT);
        render();
    }

    // ---------- building the cards ----------
    // Keeps the teal header at the original card's height so taller results don't squash it
    function keepHeaderHeight(orig, card, sid) {
        const measured = orig.firstElementChild ? orig.firstElementChild.getBoundingClientRect().height : 0;
        if (measured >= 60) headerHeights[sid] = measured;           // the originals are hidden after the first render, so remember it
        const h = headerHeights[sid] || 140;
        Object.assign(card.style, { height: 'auto', maxHeight: 'none', overflow: 'visible' });
        const head = card.firstElementChild;
        if (head) Object.assign(head.style, { flex: '0 0 auto', height: h + 'px', minHeight: h + 'px' });
        const bottom = card.children[1] || card.appendChild(document.createElement('div'));    // the progress area stays
        Object.assign(bottom.style, { flex: '0 0 auto', height: 'auto', minHeight: '0' });
        bottom.style.display = SETTINGS.showProgress ? '' : 'none';
    }

    // The soonest class that hasn't ended, across all courses
    function findNextClass(cards) {
        const nowSec = Date.now() / 1000;
        let best = null;
        cards.forEach(a => {
            const sid = cardSid(a), n = schedule[sid] && schedule[sid].next;
            if (n && n.class_end_dt > nowSec && (!best || n.class_start_dt < best.n.class_start_dt)) best = { sid, n };
        });
        return best;
    }

    function buildCard({ orig, sid, isNext, html }, grid) {
        const card = orig.cloneNode(true);                           // the real card: header, badge, dates, progress
        card.dataset.sid = sid;
        keepHeaderHeight(orig, card, sid);
        if (isNext) Object.assign(card.style, { outline: `3px solid ${rgb(P.teal)}`, outlineOffset: '2px', boxShadow: `0 0 14px ${rgb(P.teal, .55)}` });

        const pad = orig.children[1] ? getComputedStyle(orig.children[1]).paddingLeft : '16px';
        const results = document.createElement('div');
        results.style.cssText = `padding:0 ${pad} ${pad};flex:0 0 auto;width:100%;box-sizing:border-box;align-self:stretch;`;
        results.innerHTML = html;
        results.querySelectorAll('button[data-join]').forEach(b => b.addEventListener('click', e => {
            e.preventDefault();
            e.stopPropagation();                                     // don't trigger the card's own click
            if (!b.disabled) joinClass(b.getAttribute('data-cid'), b);
        }));
        card.appendChild(results);

        card.addEventListener('click', e => {
            if (e.ctrlKey || e.metaKey || e.shiftKey || e.altKey || e.button !== 0) return;   // let the browser open it in a new tab or window
            e.preventDefault();
            orig.click();                                            // use the site's own navigation
        });
        enableDrag(card, grid, sid);
        return card;
    }

    function createGrid(container) {
        const grid = container.cloneNode(false);                     // keeps the site's own grid styling
        grid.classList.remove('moduleCardContainer');
        grid.id = 'myAIE-grid';
        grid.addEventListener('dragover', e => { if (dragging) { e.preventDefault(); setMove(e); } });
        grid.addEventListener('drop', e => e.preventDefault());
        return grid;
    }

    function buildBody(container, parts) {
        if (!parts.length) {
            const note = document.createElement('div');
            note.id = 'myAIE-note';
            note.style.cssText = 'padding:24px 0;opacity:.7';
            note.textContent = 'All courses are hidden. Open Settings to show them.';
            return note;
        }
        const grid = createGrid(container);
        parts.forEach(part => grid.appendChild(buildCard(part, grid)));
        return grid;
    }

    function headerMarkup(allMarks) {
        const overall = SETTINGS.showPercent
            ? `<span style="font-size:13px;font-weight:600;opacity:.7"> &middot; overall average ${fmtAvg(allMarks)} (unweighted, ${allMarks.length} marked)</span>` : '';
        const options = SORT_MODES.map(([key, label]) => `<option value="${key}"${key === SORT ? ' selected' : ''}>${esc(label)}</option>`).join('');
        return `<div style="font-size:20px;font-weight:700">My Courses
            ${overall}
            <button id="myAIE-pdf" class="btn btn-primary btn-sm" style="margin-left:10px;vertical-align:middle">Summary<i class="fal fa-download" style="margin-left: 8px;"></i></button>
            <button id="myAIE-exams" class="btn btn-primary btn-sm" style="margin-left:8px;vertical-align:middle">Exam dates<i class="fal fa-calendar-days" style="margin-left: 8px;"></i></button>
            <select id="myAIE-sort" class="form-control form-control-sm" aria-label="Sort courses" title="Sort courses" style="display:inline-block;width:auto;margin-left:8px;vertical-align:middle">${options}</select></div>
            <div style="font-size:12px;opacity:.7">Drag cards to reorder &middot; <a href="#" id="myAIE-reset" style="color:inherit;text-decoration:underline">reset order</a> &middot; ${esc(statusText)}</div>`;
    }

    function buildHeader(html) {
        const head = document.createElement('div');
        head.id = 'myAIE-head';
        head.style.cssText = 'display:flex;justify-content:space-between;align-items:baseline;flex-wrap:wrap;gap:8px;margin-bottom:12px;';
        head.innerHTML = html;
        head.querySelector('#myAIE-reset').onclick = e => { e.preventDefault(); localStorage.removeItem(KEYS.order); render(); };
        head.querySelector('#myAIE-pdf').onclick = e => { e.preventDefault(); openPdfPicker(); };
        head.querySelector('#myAIE-exams').onclick = e => { e.preventDefault(); downloadExamPdf(); };
        head.querySelector('#myAIE-sort').onchange = e => setSort(e.target.value);
        return head;
    }

    function render() {
        if (dragging) return;
        const container = getContainer();
        const all = container ? getAllCards(container) : [];
        if (!all.length) return;
        rememberCourses(all);
        const cards = getCards(container);                           // may be empty if every course is hidden in Settings
        renderedSig = sigOf(cards);

        let host = document.getElementById('myAIE-results');
        if (!host) { host = document.createElement('div'); host.id = 'myAIE-results'; host.style.cssText = 'margin:0 0 8px;width:100%;'; }
        if (container.previousElementSibling !== host) container.before(host);
        ensureStyles();

        // Work out what everything should say first, so the parts that haven't changed can be left alone.
        // (Rebuilding them would close an open dropdown and make the cards flicker.)
        const data = loadGrades(), best = findNextClass(cards), allMarks = [];
        const parts = sortCards(cards, data).map(orig => {
            const sid = cardSid(orig);
            const isNext = SETTINGS.showUpNext && !!best && best.sid === sid;
            const html = (isNext ? upNextHtml(best.n) : '') + examLineHtml(sid, data) + (SETTINGS.showToday ? todayHtml(sid) : '') + bodyHtml(sid, data[sid], allMarks);
            return { orig, sid, isNext, html };
        });
        const headerHtml = headerMarkup(allMarks);
        const gridKey = JSON.stringify([parts.map(p => [p.sid, p.isNext, p.html, p.orig.textContent]), SETTINGS.showProgress]);

        let head = host.querySelector('#myAIE-head'), body = host.querySelector('#myAIE-grid, #myAIE-note');
        if (!head || headerHtml !== lastHeaderKey) { head = buildHeader(headerHtml); lastHeaderKey = headerHtml; }
        if (!body || gridKey !== lastGridKey) { body = buildBody(container, parts); lastGridKey = gridKey; }
        if (head.parentElement !== host || body.parentElement !== host) host.replaceChildren(head, body);
        container.style.display = 'none';                            // hide the originals only once the replacement exists
    }

    /* =====================================================================
     * BOOT
     * ===================================================================== */
    function tick() {
        injectSettingsPage();
        syncSidebar();
        const container = getContainer();
        if (!container || !document.body) return;
        if (!getAllCards(container).length) return;
        const cards = getCards(container);

        if (!document.getElementById('myAIE-results') || sigOf(cards) !== renderedSig) render();
        const stale = cards.map(cardSid).filter(sid => isStale('grades', sid) || isStale('schedule', sid));
        if (stale.length && !running && !document.hidden) refresh(stale);
    }

    let debounce;
    new MutationObserver(() => { clearTimeout(debounce); debounce = setTimeout(tick, 400); })
        .observe(document, { childList: true, subtree: true });      // `document` exists even before <html> does
    setInterval(tick, 15000);                                        // keeps classes and countdowns fresh
    setInterval(() => { if (document.getElementById('myAIE-results')) render(); }, 30000);
    document.addEventListener('visibilitychange', () => { if (!document.hidden) tick(); });

    // Settings, order and sorting changed in another tab (for example on the settings page) apply here straight away
    window.addEventListener('storage', e => {
        if (e.key === KEYS.settings) SETTINGS = normalizeSettings(readJSON(KEYS.settings, {}));
        else if (e.key === KEYS.weights) WEIGHTS = readJSON(KEYS.weights, {});
        else if (e.key === KEYS.sort) SORT = sanitizeSort(readJSON(KEYS.sort, 'custom'));
        else if (e.key !== KEYS.order && e.key !== KEYS.grades) return;
        render();
    });
})();