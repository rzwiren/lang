param(
  [string]$Zig = "",
  [string]$OutDir = "build\\web"
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

function Get-RepoRoot {
  return Resolve-Path (Join-Path $PSScriptRoot "..")
}

function Get-ZigPath([string]$repoRoot, [string]$zigArg) {
  if ($zigArg -and (Test-Path $zigArg)) { return (Resolve-Path $zigArg).Path }

  $zigDir = Join-Path $repoRoot "build\\zig"
  $zigExe = Join-Path $zigDir "zig-windows-x86_64-0.13.0\\zig.exe"
  if (Test-Path $zigExe) { return $zigExe }

  New-Item -ItemType Directory -Force -Path $zigDir | Out-Null
  $zip = Join-Path $zigDir "zig-windows-x86_64-0.13.0.zip"
  $url = "https://ziglang.org/download/0.13.0/zig-windows-x86_64-0.13.0.zip"

  Write-Host "Downloading Zig 0.13.0 to $zip"
  Invoke-WebRequest -Uri $url -OutFile $zip

  Write-Host "Extracting Zig..."
  Expand-Archive -Force -Path $zip -DestinationPath $zigDir

  if (!(Test-Path $zigExe)) { throw "Zig download/extract failed: $zigExe missing" }
  return $zigExe
}

$repoRoot = Get-RepoRoot
Set-Location $repoRoot

$zigPath = Get-ZigPath $repoRoot $Zig
Write-Host "Using Zig: $zigPath"

$out = Join-Path $repoRoot $OutDir
New-Item -ItemType Directory -Force -Path $out | Out-Null

$wasm = Join-Path $out "lang.wasm"

& $zigPath cc `
  -target wasm32-freestanding `
  -O2 -DNDEBUG `
  .\\l.c `
  -o $wasm `
  "-Wl,--no-entry" `
  "-Wl,--export=lang_init" `
  "-Wl,--export=lang_alloc" `
  "-Wl,--export=lang_eval" `
  "-Wl,--export=lang_last_len" `
  "-Wl,--export-memory"

Copy-Item -Force .\\web\\index.html (Join-Path $out "index.html")
Copy-Item -Force .\\web\\lang.js (Join-Path $out "lang.js")

Write-Host "Built $wasm"
Write-Host "Open a local server in $out, e.g.:"
Write-Host "  python -m http.server"
