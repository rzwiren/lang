// Serve the WASM demo assets from build/web using Lang code.
// Prereq: run `scripts/build_wasm.ps1` so `build/web/lang.wasm` exists.

// Pick a docroot that works whether you run from the repo root or from `build\`.
docroot: "misc/web"

h:{[path]
  // Map "/" -> "/index.html", otherwise use the requested path directly.
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
  if[1~(r@0);
    (200;ct;(r@1));
    (404;"text/plain"; "missing: ",fn)]
}

8080 webapp h
