# Networking / IPC

Lang has a minimal TCP socket surface (implemented directly on WinSock / POSIX sockets) plus tiny HTTP helpers.

## Verbs

- `tcplisten port` -> listener handle
- `tcpaccept listener` -> connection handle
- `n tcprecv conn` -> up to `n` bytes as a char vector
- `conn tcpsend data` -> bytes sent (best-effort send-all)
- `tcpclose handle` -> missing
- `host tcpconnect port` -> connection handle (`host` must be IPv4 dotted decimal, e.g. `"127.0.0.1"`)

- `port web body` -> blocks forever and serves `body` as `text/plain`
- `port webbg body` -> starts fixed-response server in background (Windows only)
- `webstop handle` -> stop a `webbg` / `webappbg` server (Windows only)

- `port webapp handler` -> blocks forever; calls `handler[path]` and serves `(status; type; body)` or `(type; body)`
- `port webappbg handler` -> starts `webapp` in background (Windows only; handler evaluation happens on the main thread so the REPL stays responsive)

## Example: web server

Run `misc/web.l` (uses `webbg`, so you still get the REPL):

```powershell
.\l.exe misc\web.l
```

Then visit `http://127.0.0.1:8080/`.

## Example: demo site server (Lang handler)

After building the WASM demo (`scripts/build_wasm.ps1`), run:

```powershell
.\l.exe misc\site_server.l
```

Then open `http://127.0.0.1:8080/`.
