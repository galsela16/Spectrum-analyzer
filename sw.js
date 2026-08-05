// bump CACHE version whenever you change files
const CACHE = 'rta-v92';
const ASSETS = [
  './',
  './index.html',
  './app.js',
  './recorder-worklet.js',
  './manifest.webmanifest',
  './icons/icon-192.png',
  './icons/icon-512.png',
  './icons/icon-512-maskable.png'
];

self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(ASSETS)).then(() => self.skipWaiting()));
});

self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys().then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k))))
          .then(() => self.clients.claim())
  );
});

// code (html/js/worklets): network-first so new deploys show up immediately; offline falls back to cache.
// other assets (icons/manifest): cache-first for speed.
self.addEventListener('fetch', e => {
  if (e.request.method !== 'GET') return;
  const d = e.request.destination;
  const codeLike = e.request.mode === 'navigate' || d === 'document' || d === 'script' || d === 'worker' || d === 'audioworklet' || e.request.url.endsWith('.js');
  if (codeLike) {
    e.respondWith(
      fetch(e.request).then(r => {
        const copy = r.clone();
        caches.open(CACHE).then(c => c.put(e.request, copy));
        return r;
      }).catch(() => caches.match(e.request).then(h => h || caches.match('./index.html')))
    );
  } else {
    e.respondWith(caches.match(e.request).then(h => h || fetch(e.request)));
  }
});
