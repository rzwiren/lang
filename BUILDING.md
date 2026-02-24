# Building

This repo is a single-file C program (`l.c`) and can be built with multiple compilers.
The canonical commands (the ones to prefer) are listed first.

## Windows (MSVC `cl`) — canonical

Run from a Visual Studio / Build Tools developer prompt so `cl.exe` is on `PATH`:

```powershell
cl l.c /GL /O1 /Gy /MD /DNDEBUG /link /LTCG /OPT:REF /OPT:ICF Ws2_32.lib
```

Output: `l.exe` (plus `l.obj`, `l.pdb`, etc. depending on your settings).

Script wrapper:

```powershell
.\scripts\build.ps1
```

Output: `.\build\l.exe`

If PowerShell blocks scripts, try:

```powershell
powershell -ExecutionPolicy Bypass -File .\scripts\build.ps1
```

## Linux / WSL (any `cc`) — canonical

Release build:

```sh
cc -Os l.c -o l_lin
```

ASAN build:

```sh
cc -fsanitize=address l.c -o l_lin_asan
```

Script wrapper:

```sh
./scripts/build.sh release
./scripts/build.sh asan
```

If it isn't executable:

```sh
chmod +x ./scripts/build.sh
```

Outputs: `./build/l_lin` and `./build/l_lin_asan`

## Optional: `zig cc` fallback

If you don't have a system compiler handy, `zig cc` can usually stand in for `cc`.
Use the same flags as the corresponding `cc` command.

## Tests

After building `l.exe`, run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File test\run_tests.ps1
```

## No libc allocators (important)

`l.c` must not call the C standard library heap allocation APIs:

- `malloc`, `calloc`, `realloc`, `free`

Lang objects should be allocated via the arena allocators (`tsna`/`vna`/etc.). Temporary C-side buffers (lexer token buffers, REPL input lines, etc.) use the OS-backed helpers `os_heap_alloc`/`os_heap_free` (defined in `l.c`).
