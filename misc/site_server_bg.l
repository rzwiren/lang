// Background variant of `misc/site_server.l`.
// Windows only: uses `webappbg` so the REPL stays responsive.
// Prereq: run `scripts/build_wasm.ps1` so `build/web/lang.wasm` exists.

// Pick a docroot that works whether you run from the repo root or from `build\`.

h:{[path]
  pr path
  docroot:"misc/web"
  p:path
  fn: docroot,if["/"~p;            "/index.html"
                "/index.html"~p;   "/index.html"
                "/lang.js"~p;      "/lang.js"
                "/lang.wasm"~p;    "/lang.wasm"
                                 "/index.html"]
  ct: if["/"~p; "text/html"
         "/index.html"~p; "text/html"
         "/lang.js"~p; "text/javascript"
         "/lang.wasm"~p; "application/wasm"
         "text/plain"]
  r:texttry fn
  if[1~(r@0)
    (200;ct;(r@1))
    (404;"text/plain"; "missing: ",fn)]
}

srv:8080 webappbg h
srv
