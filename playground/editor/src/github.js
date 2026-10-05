// GitHub (Primer) light and dark themes for CodeMirror 6.
import { EditorView } from "@codemirror/view"
import { HighlightStyle, syntaxHighlighting } from "@codemirror/language"
import { tags as t } from "@lezer/highlight"

const light = {
  fg: "#1f2328", bg: "#ffffff", subtle: "#f6f8fa", border: "#d0d7de", muted: "#59636e", lineNumber: "#8c959f",
  accent: "#0969da", selection: "#54aeff66", match: "#d4a72c66", activeLine: "#eaeef280",
  comment: "#59636e", keyword: "#cf222e", string: "#0a3069", constant: "#0550ae", entity: "#6639ba", variable: "#953800",
  invalidFg: "#f6f8fa", invalidBg: "#82071e",
}
const dark = {
  fg: "#e6edf3", bg: "#0d1117", subtle: "#161b22", border: "#30363d", muted: "#8b949e", lineNumber: "#6e7681",
  accent: "#58a6ff", selection: "#388bfd66", match: "#bb800966", activeLine: "#6e76811a",
  comment: "#8b949e", keyword: "#ff7b72", string: "#a5d6ff", constant: "#79c0ff", entity: "#d2a8ff", variable: "#ffa657",
  invalidFg: "#f0f6fc", invalidBg: "#8e1519",
}

function github(c, isDark) {
  const theme = EditorView.theme({
    "&": { color: c.fg, backgroundColor: c.bg, fontSize: "12px" },
    ".cm-scroller": { fontFamily: 'ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, "Liberation Mono", monospace', lineHeight: "20px" },
    ".cm-content": { caretColor: c.accent },
    ".cm-cursor, .cm-dropCursor": { borderLeftColor: c.accent },
    "&.cm-focused > .cm-scroller > .cm-selectionLayer .cm-selectionBackground, .cm-selectionBackground, .cm-content ::selection": { backgroundColor: c.selection },
    ".cm-activeLine": { backgroundColor: c.activeLine },
    ".cm-gutters": { backgroundColor: c.bg, color: c.lineNumber, border: "none" },
    ".cm-activeLineGutter": { backgroundColor: c.activeLine, color: c.fg },
    ".cm-selectionMatch, .cm-searchMatch": { backgroundColor: c.match },
    "&.cm-focused .cm-matchingBracket": { backgroundColor: c.selection },
    "&.cm-focused .cm-nonmatchingBracket": { color: c.keyword },
    ".cm-foldPlaceholder": { backgroundColor: c.subtle, border: `1px solid ${c.border}`, color: c.muted },
    ".cm-tooltip": { backgroundColor: c.bg, border: `1px solid ${c.border}`, color: c.fg },
    ".cm-tooltip-autocomplete ul li[aria-selected]": { backgroundColor: c.subtle, color: c.fg },
    ".cm-panels": { backgroundColor: c.subtle, color: c.fg, borderColor: c.border },
  }, { dark: isDark })

  const highlight = HighlightStyle.define([
    { tag: t.comment, color: c.comment },
    { tag: [t.keyword, t.modifier], color: c.keyword },
    { tag: [t.string, t.special(t.string)], color: c.string },
    { tag: t.content, color: c.fg }, // plain text nested in a styled subtree, e.g. string interpolations
    { tag: [t.number, t.bool, t.null, t.atom, t.escape, t.self, t.operator], color: c.constant },
    { tag: t.definitionOperator, color: c.fg },
    { tag: [t.function(t.variableName), t.function(t.definition(t.variableName)), t.function(t.propertyName),
            t.typeName, t.definition(t.typeName), t.className, t.namespace], color: c.entity },
    { tag: [t.local(t.variableName), t.annotation, t.meta], color: c.variable },
    { tag: t.invalid, color: c.invalidFg, backgroundColor: c.invalidBg },
  ])
  return [theme, syntaxHighlighting(highlight)]
}

export const githubLight = github(light, false)
export const githubDark = github(dark, true)
