const encoder = new TextEncoder();
const decoder = new TextDecoder("utf-8");

const runBtn = document.getElementById("run");
const clearBtn = document.getElementById("clear");
const resetBtn = document.getElementById("reset");
const ex1Btn = document.getElementById("ex1");
const ex2Btn = document.getElementById("ex2");
const ex3Btn = document.getElementById("ex3");
const statusEl = document.getElementById("status");
const termEl = document.getElementById("term");
const promptEl = document.getElementById("prompt");

function termAppend(s) {
  termEl.textContent += s;
  termEl.scrollTop = termEl.scrollHeight;
}

function termClear() {
  termEl.textContent = "";
}

function promptAutosize() {
  promptEl.style.height = "auto";
  const h = Math.min(promptEl.scrollHeight, 240);
  promptEl.style.height = `${h}px`;
}

async function instantiateRuntime() {
  let stdoutBuf = "";
  let stderrBuf = "";
  let memoryRef = null;

  const imports = {
    env: {
      l_wasm_write_stdout(ptr, len) {
        if (!memoryRef) return;
        const bytes = new Uint8Array(memoryRef.buffer, ptr, len);
        stdoutBuf += decoder.decode(bytes);
      },
      l_wasm_write_stderr(ptr, len) {
        if (!memoryRef) return;
        const bytes = new Uint8Array(memoryRef.buffer, ptr, len);
        stderrBuf += decoder.decode(bytes);
      },
    },
  };

  const fetchAndInstantiate = async () => {
    const resp = await fetch("./lang.wasm");
    const bytes = await resp.arrayBuffer();
    return WebAssembly.instantiate(bytes, imports);
  };

  let instance;
  try {
    const result = await WebAssembly.instantiateStreaming(fetch("./lang.wasm"), imports);
    instance = result.instance;
  } catch {
    const result = await fetchAndInstantiate();
    instance = result.instance;
  }

  const { memory, lang_init, lang_alloc, lang_eval, lang_last_len } = instance.exports;
  memoryRef = memory;
  lang_init();

  const evalLang = (src) => {
    stdoutBuf = "";
    stderrBuf = "";

    const bytes = encoder.encode(src);
    const ptr = lang_alloc(bytes.length);
    new Uint8Array(memory.buffer, ptr, bytes.length).set(bytes);

    const outPtr = lang_eval(ptr, bytes.length);
    const outLen = lang_last_len();
    const outBytes = new Uint8Array(memory.buffer, outPtr, outLen);
    const value = decoder.decode(outBytes);

    return { value, stdout: stdoutBuf, stderr: stderrBuf };
  };

  return { evalLang };
}

let runtime = null;
let running = false;
const history = [];
let histIdx = 0;

function setUiReady(ready) {
  runBtn.disabled = !ready;
  clearBtn.disabled = !ready;
  resetBtn.disabled = !ready;
  ex1Btn.disabled = !ready;
  ex2Btn.disabled = !ready;
  ex3Btn.disabled = !ready;
  promptEl.disabled = !ready;
}

async function resetRuntime() {
  statusEl.textContent = "Loading...";
  setUiReady(false);
  try {
    runtime = await instantiateRuntime();
    statusEl.textContent = "Ready";
    setUiReady(true);
    promptEl.focus();
  } catch (err) {
    console.error(err);
    statusEl.textContent = "Failed to load WASM (open DevTools)";
    setUiReady(false);
    runtime = null;
  }
}

function runSource(src) {
  if (!runtime) return;
  const trimmed = src.trim();
  if (!trimmed) return;

  if (history.length === 0 || history[history.length - 1] !== src) history.push(src);
  histIdx = history.length;

  termAppend(` ${src}\n`);

  let r;
  try {
    r = runtime.evalLang(src);
  } catch (e) {
    termAppend(`err: ${String(e)}\n`);
    return;
  }

  if (r.stdout) termAppend(r.stdout);
  if (r.stderr) termAppend(r.stderr);
  termAppend(r.value + "\n");
}

function runPrompt() {
  if (running) return;
  const src = promptEl.value;
  if (!src.trim()) return;
  running = true;
  try {
    runSource(src);
  } finally {
    running = false;
    promptEl.value = "";
    promptAutosize();
    promptEl.focus();
  }
}

function histPrev() {
  if (!history.length) return;
  if (histIdx <= 0) histIdx = 0;
  else histIdx--;
  promptEl.value = history[histIdx] ?? "";
  promptAutosize();
}

function histNext() {
  if (!history.length) return;
  if (histIdx >= history.length) {
    histIdx = history.length;
    promptEl.value = "";
  } else {
    histIdx++;
    promptEl.value = history[histIdx] ?? "";
  }
  promptAutosize();
}

promptEl.addEventListener("input", promptAutosize);

promptEl.addEventListener("keydown", (e) => {
  if (e.key === "Enter" && !e.shiftKey) {
    e.preventDefault();
    runPrompt();
    return;
  }

  const isSingleLine = !promptEl.value.includes("\n");
  if (!isSingleLine) return;

  if (e.key === "ArrowUp") {
    e.preventDefault();
    histPrev();
    return;
  }
  if (e.key === "ArrowDown") {
    e.preventDefault();
    histNext();
    return;
  }
});

runBtn.addEventListener("click", runPrompt);

clearBtn.addEventListener("click", () => {
  termClear();
  promptEl.focus();
});

resetBtn.addEventListener("click", async () => {
  termClear();
  termAppend("reset\n");
  await resetRuntime();
});

function setPrompt(src) {
  promptEl.value = src;
  promptAutosize();
  promptEl.focus();
}

ex1Btn.addEventListener("click", () => setPrompt('"hello from wasm"'));
ex2Btn.addEventListener("click", () => setPrompt("!10"));
ex3Btn.addEventListener("click", () => setPrompt("{[x] x+x}[21]"));

setUiReady(false);
termAppend("Lang WASM REPL\n");
termAppend('Try: "hello from wasm"\n');
termAppend("Try: !10\n");
termAppend("Try: {[x] x+x}[21]\n\n");
resetRuntime().then(() => promptAutosize());
