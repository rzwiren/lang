# Networking / IPC

Lang has a minimal TCP socket surface (implemented directly on WinSock / POSIX sockets) plus a tiny fixed-response HTTP server.

## Verbs

- `tcplisten port` → listener handle
- `tcpaccept listener` → connection handle
- `n tcprecv conn` → up to `n` bytes as a char vector
- `conn tcpsend data` → bytes sent (best-effort send-all)
- `tcpclose handle` → missing
- `host tcpconnect port` → connection handle (`host` must be IPv4 dotted decimal, e.g. `"127.0.0.1"`)
- `port web body` → blocks forever and serves `body` as `text/plain`
- `port webbg body` → starts server in background (Windows only)
- `webstop handle` → stop a `webbg` server (Windows only)

## Example: web server

Run `misc/web.l` (uses `webbg`, so you still get the REPL):

```powershell
.\l.exe misc\web.l
```

Then visit `http://127.0.0.1:8080/`.
