param(
  [ValidateSet('release','clean')]
  [string]$Target = 'release'
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot '..')
Set-Location $repoRoot

$buildDir = Join-Path $repoRoot 'build'

if ($Target -eq 'clean') {
  if (Test-Path $buildDir) { Remove-Item -Recurse -Force $buildDir }
  Write-Host "Cleaned $buildDir"
  exit 0
}

if (-not (Get-Command cl -ErrorAction SilentlyContinue)) {
  throw "MSVC 'cl' not found on PATH. Run this from a Visual Studio / Build Tools Developer Command Prompt."
}

New-Item -ItemType Directory -Force -Path $buildDir | Out-Null

$outExe = Join-Path $buildDir 'l.exe'

& cl `
  l.c `
  /nologo `
  /GL /O1 /Gy /MD /DNDEBUG `
  /Fe:$outExe `
  /Fo"$buildDir\\" `
  /link /LTCG /OPT:REF /OPT:ICF Ws2_32.lib

Write-Host "Built $outExe"
