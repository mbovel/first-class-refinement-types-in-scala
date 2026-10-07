import { EditorView, basicSetup } from "codemirror"
import { keymap } from "@codemirror/view"
import { Compartment } from "@codemirror/state"
import { indentWithTab } from "@codemirror/commands"
import { scalaTreeSitter } from "./treesitter.js"
import { githubLight, githubDark } from "./github.js"

import catalogue from "../examples.json"

// Bundled at build time, so the page needs nothing but itself once loaded. The catalogue
// gives the order and the labels; this gives the text.
const sources = import.meta.glob("../examples/*.scala", {
  query: "?raw",
  eager: true,
  import: "default",
})

const examples = catalogue.map(({ label, file }) => ({
  label,
  text: sources[`../examples/${file}`],
}))

const chooser = document.getElementById("example")
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
  doc: examples[0].text,
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

for (const [index, { label }] of examples.entries()) {
  chooser.add(new Option(label, String(index)))
}

chooser.addEventListener("change", event => {
  view.dispatch({
    changes: { from: 0, to: view.state.doc.length, insert: examples[event.target.value].text },
  })
  // The old diagnostics describe the program that was just replaced.
  output.textContent = ""
  output.hidden = true
  status.textContent = ""
  view.focus()
})

button.addEventListener("click", compile)
button.disabled = false
status.textContent = ""
