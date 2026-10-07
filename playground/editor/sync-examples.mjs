// Refreshes examples/ from the compiler's own test suite.
//
// The copies are committed rather than read at build time: the dotty submodule is a 131 MB
// working tree, and the website workflow deliberately does not clone it, for two kilobytes
// of Scala. Run this after changing examples.json or after the submodule moves.
import { readFileSync, writeFileSync, existsSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const repo = join(here, "..", "..") // public/
const examples = JSON.parse(readFileSync(join(here, "examples.json"), "utf8"))

let changed = 0
let missing = 0

for (const { label, file, source } of examples) {
  const target = join(here, "examples", file)
  if (!source) {
    if (!existsSync(target)) {
      console.error(`${label}: ${file} has no source and does not exist`)
      missing++
    }
    continue
  }
  const from = join(repo, source)
  if (!existsSync(from)) {
    console.error(`${label}: ${source} not found (is the submodule checked out?)`)
    missing++
    continue
  }
  const content = readFileSync(from, "utf8")
  const before = existsSync(target) ? readFileSync(target, "utf8") : null
  if (content !== before) {
    writeFileSync(target, content)
    console.log(`${label}: updated from ${source}`)
    changed++
  }
}

console.log(`${examples.length} examples, ${changed} updated`)
if (missing > 0) process.exit(1)
