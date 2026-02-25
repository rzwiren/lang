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
  $lines = @($lines)
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
  $lines = @($lines)

  # Filter interpreter startup diagnostics so we only assert on user-level output.
  $userLines = @($lines | Where-Object { $_ -notmatch '^AB\[' -and $_ -notmatch '^rem ord' })

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
Invoke-LangScript "test\\int_heap64_pos.l" "576460752303423488"
Invoke-LangScript "test\\int_heap64_neg.l" "-576460752303423489"
Invoke-LangScript "test\\bench_ticks.l" "1"
Invoke-LangScript "test\\eval_bench.l" "1"
Invoke-LangScript "test\\inplace_bench_allocs.l" "1"
Invoke-LangScript "test\\inplace_unary_bench_allocs.l" "1"
Invoke-LangScript "test\\inplace_cmp_bench_allocs.l" "1"
Invoke-LangScriptExpectNoValue "test\\semicolon_suppress_print.l"
Invoke-LangScript "test\\symbol_intern.l" "1"
Invoke-LangScript "test\\symbol_print.l" '`abc'
Invoke-LangScript "test\\symmap_print.l" "1"
Invoke-LangScript "test\\symbol_list_literal.l" "1"
Invoke-LangScript "test\\tag64.l" "1"
Invoke-LangScript "test\\bracket_index.l" "1"
Invoke-LangScript "test\\dotref_index.l" "1"
Invoke-LangScript "test\\dotref_set_depth.l" "1"
Invoke-LangScript "test\\if_lazy.l" "1"
Invoke-LangScript "test\\lambda_apply.l" "1"
Invoke-LangScript "test\\lambda_struct_key.l" "1"
Invoke-LangScript "test\\bracket_call.l" "1"
Invoke-LangScript "test\\parens_delistify.l" "1"
Invoke-LangScript "test\\lexer_parity.l" "1"
Invoke-LangScript "test\\string_escape.l" "1"
Invoke-LangScript "test\\text_io.l" "1"
Invoke-LangScript "test\\texttry.l" "1"
Invoke-LangScript "test\\site_handler.l" "1"
Invoke-LangScript "test\\tcp_smoke.l" "1"

function Invoke-WebAppBgSmoke() {
  if ($env:LANG_WEB_SMOKE -ne "1") {
    Write-Host "SKIP webappbg smoke (set LANG_WEB_SMOKE=1 to enable)"
    return
  }
  if ($env:OS -ne "Windows_NT") {
    Write-Host "SKIP webappbg smoke (not Windows)"
    return
  }
  if (!(Test-Path $Exe)) { throw "Missing interpreter: $Exe (build it first)" }

  # Find a free TCP port to avoid flakes.
  $port = $null
  foreach ($p in 18080..18150) {
    try {
      $l = [System.Net.Sockets.TcpListener]::new([System.Net.IPAddress]::Loopback, $p)
      $l.Start()
      $l.Stop()
      $port = $p
      break
    } catch {
      continue
    }
  }
  if (-not $port) { throw "No free port found for webappbg smoke test" }

  $tmpFn = Join-Path (Get-Location) "test_tmp_webappbg.txt"
  "ok-from-file" | Out-File -Encoding ascii -NoNewline $tmpFn

  $stdout = New-Object System.Text.StringBuilder
  $stderr = New-Object System.Text.StringBuilder

  $psi = New-Object System.Diagnostics.ProcessStartInfo
  $psi.FileName = (Resolve-Path $Exe).Path
  $psi.RedirectStandardInput = $true
  $psi.RedirectStandardOutput = $true
  $psi.RedirectStandardError = $true
  $psi.UseShellExecute = $false
  $psi.CreateNoWindow = $true

  $proc = New-Object System.Diagnostics.Process
  $proc.StartInfo = $psi

  $null = $proc.Start()
  $proc.OutputDataReceived += { param($s,$e) if($e.Data){ [void]$stdout.AppendLine($e.Data) } }
  $proc.ErrorDataReceived += { param($s,$e) if($e.Data){ [void]$stderr.AppendLine($e.Data) } }
  $proc.BeginOutputReadLine()
  $proc.BeginErrorReadLine()

  try {
    $proc.StandardInput.WriteLine('h:{[p] r:texttry "test_tmp_webappbg.txt"; if[1~(r@0); (200;"text/plain";(r@1)); (404;"text/plain";"missing")]}')
    $proc.StandardInput.WriteLine("srv:${port} webappbg h")
    Start-Sleep -Milliseconds 250

    $uri = "http://127.0.0.1:${port}/"
    $resp = Invoke-WebRequest -UseBasicParsing -Uri $uri -TimeoutSec 5
    if ($resp.Content -ne "ok-from-file") {
      throw "webappbg smoke: expected body 'ok-from-file', got '$($resp.Content)'"
    }

    $proc.StandardInput.WriteLine("webstop srv")
    $proc.StandardInput.WriteLine('\\')
    $proc.StandardInput.Flush()
    $proc.StandardInput.Close()

    if (-not $proc.WaitForExit(5000)) {
      $proc.Kill()
      throw "webappbg smoke: interpreter did not exit"
    }

    Write-Host "PASS webappbg smoke"
  } catch {
    $outDump = $stdout.ToString()
    $errDump = $stderr.ToString()
    throw "FAIL webappbg smoke: $($_.Exception.Message)`n--- stdout ---`n$outDump`n--- stderr ---`n$errDump"
  } finally {
    if (Test-Path $tmpFn) { Remove-Item -Force $tmpFn }
    if (!$proc.HasExited) { try { $proc.Kill() } catch {} }
  }
}

Invoke-WebAppBgSmoke
