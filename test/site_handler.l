// Unit-test the web handler logic without sockets.

docroot:"test"
idx:docroot,"\\tmp_site_index.html"
js: docroot,"\\tmp_site_lang.js"
miss: docroot,"\\tmp_site_missing.txt"

idx text "<h1>ok</h1>"
js text "console.log('ok')"

h:{[path]
  p:path
  fn: if["/"~p;            idx;
          "/index.html"~p; idx;
          "/lang.js"~p;    js;
          "/missing"~p;    miss;
          miss]
  ct: if["/"~p; "text/html";
         "/index.html"~p; "text/html";
         "/lang.js"~p; "text/javascript";
         "text/plain"]
  r:texttry fn
  if[1~(r@0);
    (200;ct;(r@1));
    (404;"text/plain";"missing")]
}

r0:h["/"]
t0: 200~(r0@0)

r1:h["/lang.js"]
t1: 200~(r1@0)

r2:h["/missing"]
t2: 404~(r2@0)
t3: "missing"~(r2@2)

t0*t1*t2*t3
