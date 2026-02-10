param(
  [string]$Exe = ".\\l.exe"
)

$ErrorActionPreference = "Stop"

function Invoke-LangScript([string]$scriptPath, [string]$expectedLastValue) {
  if (!(Test-Path $scriptPath)) { throw "Missing test script: $scriptPath" }
  if (!(Test-Path $Exe)) { throw "Missing interpreter: $Exe (build it first)" }

  $out = & $Exe $scriptPath 2>&1 | ForEach-Object { "$_" }

  $lines = $out | Where-Object { $_ -ne $null } | ForEach-Object { $_.TrimEnd() }
  $lines = $lines | Where-Object { $_.Trim() -ne "" -and $_ -ne " " }
  if ($lines.Count -eq 0) { throw "No output for $scriptPath" }

  $last = $lines[-1].Trim()
  if ($last -ne $expectedLastValue) {
    throw "FAIL ${scriptPath}: expected last='${expectedLastValue}' got last='${last}'"
  }
  Write-Host "PASS ${scriptPath}"
}

function Invoke-LangScriptExpectNoValue([string]$scriptPath) {
  if (!(Test-Path $scriptPath)) { throw "Missing test script: $scriptPath" }
  if (!(Test-Path $Exe)) { throw "Missing interpreter: $Exe (build it first)" }

  $out = & $Exe $scriptPath 2>&1 | ForEach-Object { "$_" }

  $lines = $out | Where-Object { $_ -ne $null } | ForEach-Object { $_.TrimEnd() }
  $lines = $lines | Where-Object { $_.Trim() -ne "" -and $_ -ne " " }

  # Filter interpreter startup diagnostics so we only assert on user-level output.
  $userLines = $lines | Where-Object { $_ -notmatch '^AB\[' -and $_ -notmatch '^rem ord' }

  if ($userLines.Count -ne 0) {
    $last = $userLines[-1].Trim()
    throw "FAIL ${scriptPath}: expected no value output, got last='${last}'"
  }
  Write-Host "PASS ${scriptPath} (no value)"
}

Invoke-LangScript "test\\match.l" "1"
Invoke-LangScript "test\\dict_grow.l" "79"
Invoke-LangScript "test\\dict_struct_key.l" "1"
Invoke-LangScript "test\\dict_at.l" "1"
Invoke-LangScript "test\\float.l" "1"
Invoke-LangScript "test\\minus_lex.l" "1"
Invoke-LangScript "test\\div_mod.l" "1"
Invoke-LangScript "test\\bench_ticks.l" "1"
Invoke-LangScript "test\\eval_bench.l" "1"
Invoke-LangScriptExpectNoValue "test\\semicolon_suppress_print.l"
Invoke-LangScript "test\\symbol_intern.l" "1"
Invoke-LangScript "test\\symbol_print.l" '`abc'
Invoke-LangScript "test\\symmap_print.l" "1"
Invoke-LangScript "test\\symbol_list_literal.l" "1"
Invoke-LangScript "test\\tag64.l" "1"
Invoke-LangScript "test\\bracket_index.l" "1"
Invoke-LangScript "test\\if_lazy.l" "1"
Invoke-LangScript "test\\lambda_apply.l" "1"
Invoke-LangScript "test\\bracket_call.l" "1"
