import { defineConfig } from "vite"

// A standalone page, built into the published site at website/playground/. Relative base
// so it resolves its own bundle and .wasm files from whichever subdirectory it is served
// under (matt.bovel.net/scala-refinement-types/playground/).
export default defineConfig({
  base: "./",
  build: {
    outDir: "../../website/playground",
    emptyOutDir: true,
    // web-tree-sitter's glue code, and src/main.js, use top-level await.
    target: "es2022",
  },
})
