import { EditorView, basicSetup } from "codemirror"
import { keymap } from "@codemirror/view"
import { Compartment } from "@codemirror/state"
import { indentWithTab } from "@codemirror/commands"
import { scalaTreeSitter } from "./treesitter.js"
import { githubLight, githubDark } from "./github.js"

const example = `def max(x: Int, y: Int): { v: Int with v >= x && v >= y } =
  if (x > y) x else y

// Try swapping the branches above, then compile again.
val m: { v: Int with v >= 3 } = max(3, 7)
`

const mount = document.getElementById("editor")
const button = document.getElementById("run")
const status = document.getElementById("status")
const output = document.getElementById("output")
const endpoint = mount.dataset.endpoint

const prefersDark = matchMedia("(prefers-color-scheme: dark)")
const themeFor = isDark => (isDark ? githubDark : githubLight)
const theme = new Compartment()

let running = false

async function compile() {
  if (running) return
  running = true
  button.disabled = true
  status.textContent = "Compiling…"
  try {
    // text/plain keeps this a CORS-simple request, so there is no preflight.
    const response = await fetch(endpoint, {
      method: "POST",
      headers: { "Content-Type": "text/plain;charset=UTF-8" },
      body: view.state.doc.toString(),
    })
    const text = (await response.text()).replace(/\s+$/, "")
    output.textContent = text
    output.hidden = text === ""
    if (response.ok) status.textContent = text === "" ? "Compiled, no errors." : ""
    else status.textContent = `The compiler service answered ${response.status}.`
  } catch (error) {
    status.textContent = "Could not reach the compiler service."
    output.textContent = String(error)
    output.hidden = false
  } finally {
    running = false
    button.disabled = false
  }
}

// Top-level await: the tree-sitter grammar is WebAssembly and has to be fetched first.
const scala = await scalaTreeSitter()

const view = new EditorView({
  parent: mount,
  doc: example,
  extensions: [
    basicSetup,
    keymap.of([
      indentWithTab,
      { key: "Mod-Enter", preventDefault: true, run: () => (compile(), true) },
    ]),
    scala,
    theme.of(themeFor(prefersDark.matches)),
  ],
})

prefersDark.addEventListener("change", event =>
  view.dispatch({ effects: theme.reconfigure(themeFor(event.matches)) }),
)

button.addEventListener("click", compile)
button.disabled = false
status.textContent = ""
