// Minimal CodeMirror 6 <-> tree-sitter bridge.
//
// Incrementality is preserved on both sides:
//  * tree-sitter: the previous tree-sitter tree is edited (edits are derived from the
//    Lezer TreeFragments CodeMirror hands us) and passed as `oldTree` to `parse`.
//  * Lezer: top-level children whose tree-sitter node id is unchanged reuse their
//    previous Lezer subtree instead of being rebuilt (`Tree.build`'s `reused`).
//
// Highlighting is driven by the grammar's own highlights.scm query: each (node type,
// capture) pair becomes its own Lezer node type carrying the capture's style tags.
import { Parser as TSParser, Language as TSLanguage, Query } from "web-tree-sitter"
import { Parser, Tree, NodeType, NodeSet, NodeProp } from "@lezer/common"
import { styleTags, tags as t } from "@lezer/highlight"
import {
  Language, LanguageSupport, defineLanguageFacet, languageDataProp, syntaxTree,
  foldNodeProp, foldService, indentNodeProp, indentService, delimitedIndent,
} from "@codemirror/language"
import tsWasm from "web-tree-sitter/web-tree-sitter.wasm?url"
import scalaWasm from "tree-sitter-scala/tree-sitter-scala.wasm?url"
import scalaHighlights from "tree-sitter-scala/queries/highlights.scm?raw"

// Lezer tags for highlight capture names (nvim-treesitter conventions, which
// tree-sitter-scala's highlights.scm follows). Unknown names fall back to their prefix,
// e.g. "keyword.coroutine" -> "keyword".
const captureTags = {
  keyword: t.keyword, "keyword.function": t.definitionKeyword, "keyword.return": t.controlKeyword,
  "keyword.operator": t.operatorKeyword, conditional: t.controlKeyword, repeat: t.controlKeyword,
  exception: t.controlKeyword, include: t.moduleKeyword, "type.qualifier": t.modifier, storageclass: t.modifier,
  type: t.typeName, "type.definition": t.definition(t.typeName), constructor: t.typeName,
  function: t.function(t.definition(t.variableName)), method: t.function(t.definition(t.variableName)),
  "function.call": t.function(t.variableName), "method.call": t.function(t.propertyName),
  "function.builtin": t.self, "variable.builtin": t.self,
  variable: t.variableName, parameter: t.local(t.variableName), property: t.propertyName, namespace: t.namespace,
  number: t.number, float: t.number, boolean: t.bool, "constant.builtin": t.null,
  operator: t.operator, "punctuation.bracket": t.bracket, "punctuation.delimiter": t.separator,
  "punctuation.special": t.punctuation, string: t.string, comment: t.comment, attribute: t.annotation, none: t.content,
}

// The highlighter reads style rules from a NodeProp that @lezer/highlight does not export.
// Running styleTags against a throwaway node type yields both the prop and a rule. A
// capture styles its node's whole range (nested captures override inside), which is
// Lezer's "node/..." inherit mode; many captured nodes, e.g. opaque_modifier or
// boolean_literal, are wrappers around a single token and would otherwise style nothing.
const probe = NodeType.define({ id: 0, name: "probe" })
const [ruleProp] = styleTags({ probe: t.content })(probe)
const captureRules = Object.fromEntries(Object.entries(captureTags).map(([name, tag]) =>
  [name, styleTags({ "probe/...": tag })(probe)[1]]))
function ruleFor(capture) {
  for (let name = capture; ; name = name.slice(0, name.lastIndexOf("."))) {
    if (captureRules[name]) return captureRules[name]
    if (!name.includes(".")) return null
  }
}

const languageData = defineLanguageFacet({
  commentTokens: { line: "//", block: { open: "/*", close: "*/" } },
  indentOnInput: /^\s*[)\]}]$/,
})

// Bracket tokens get closedBy/openedBy props. That alone gives CodeMirror bracket
// matching and its built-in delimited indentation for any node starting with a bracket.
const brackets = { "(": ")", "[": "]", "{": "}" }
const closers = Object.fromEntries(Object.entries(brackets).map(([o, c]) => [c, o]))
const foldPairs = { ...brackets, "/*": "*/" }

const trimEnd = (doc, from, to) => {
  while (to > from && /\s/.test(doc.sliceString(to - 1, to))) to--
  return to
}

// Folding: nodes delimited by a bracket pair or comment delimiters (any grammar), and
// Scala 3 colon bodies (`class A:`, `enum E:`), which start with a ":" token.
function foldNode(node, state) {
  const first = node.firstChild, last = node.lastChild
  if (!first || first == last) return null
  if (foldPairs[first.name] == last.name) return { from: first.to, to: last.from }
  if (first.name == ":") return { from: first.to, to: trimEnd(state.doc, first.to, node.to) }
  return null
}

// Scala 3 indented blocks start on the line after their header (`def f =`, `x match`,
// `then`, `else`, ...), so they are never on the header line's node stack. A fold
// service looks at the next line instead.
const indentedBlocks = new Set(["indented_block", "indented_cases"])
const foldIndented = foldService.of((state, from, to) => {
  if (to >= state.doc.length) return null
  const next = state.doc.lineAt(to + 1), p = next.from + /^\s*/.exec(next.text)[0].length
  for (let n = syntaxTree(state).resolveInner(p, 1); n && n.from == p; n = n.parent)
    if (indentedBlocks.has(n.name)) return { from: to, to: trimEnd(state.doc, to, n.to) }
  return null
})

// Inside an indented block or colon body, align with its first member. Brace bodies
// use the standard delimited strategy.
const blockTypes = new Set([...indentedBlocks, "template_body", "enum_body"])
function blockColumn(node, cx) {
  const first = node.firstChild
  if (!first || brackets[first.name]) return null
  const body = first.name == ":" ? node.childAfter(first.to) : first
  return body ? cx.column(body.from) : cx.lineIndent(node.from) + cx.unit
}
const indentBlock = cx => blockColumn(cx.node, cx) ?? delimitedIndent({ closing: brackets[cx.node.firstChild.name] })(cx)

// A line ending in one of these tokens opens an indented region on the next line. These
// are the token-level `@indent.begin` captures of tree-sitter-scala's indents.scm
// ("=", ":", "match"), extended with the Scala 3 keywords that file lacks, plus opening
// brackets (needed when the bracket is still unclosed and tree-sitter yields an ERROR).
const lineOpeners = new Set(["=", ":", "match", "then", "else", "do", "=>", "yield", "try", "catch", "finally", ...Object.keys(brackets)])
const indentScala = indentService.of((cx, pos) => {
  const { text, from } = cx.lineAt(pos, -1), end = from + text.replace(/\s+$/, "").length
  const tok = syntaxTree(cx.state).resolveInner(end, -1)
  if (tok.to == end && lineOpeners.has(tok.name)) return cx.lineIndent(pos, -1) + cx.unit
  // At the end of the document a block ends exactly at the cursor instead of extending
  // to the next token, so CodeMirror's tree walk (which needs nodes to contain the
  // cursor) would fall through to column 0. Align with the innermost such block.
  for (let n = tok; n && n.to <= pos; n = n.parent) {
    if (!blockTypes.has(n.name)) continue
    const column = blockColumn(n, cx)
    if (column != null) return column
    // Brace body: unclosed if tree-sitter had to insert a zero-width missing "}".
    if (n.lastChild.from == n.lastChild.to) return cx.lineIndent(n.from) + cx.unit
  }
  return undefined
})

function pt(doc, pos) {
  const l = doc.lineAt(pos)
  return { row: l.number - 1, column: pos - l.from }
}

// Turn the Lezer fragments (unchanged regions, new-doc coords; old = new + offset) into
// tree-sitter edits. Edits are applied in order, so each is expressed in the coordinates
// of the intermediate document newDoc[0, nFrom) ++ oldDoc[oFrom, ∞).
function fragmentsToEdits(fragments, oldDoc, newDoc) {
  const gaps = []
  let nPos = 0, oPos = 0
  for (const f of fragments) {
    gaps.push([nPos, oPos, f.from, f.from + f.offset])
    nPos = f.to; oPos = f.to + f.offset
  }
  gaps.push([nPos, oPos, newDoc.length, oldDoc.length])
  const edits = []
  for (const [nFrom, oFrom, nTo, oTo] of gaps) {
    if (nFrom == nTo && oFrom == oTo) continue
    const startPosition = pt(newDoc, nFrom), oS = pt(oldDoc, oFrom), oE = pt(oldDoc, oTo)
    edits.push({
      startIndex: nFrom, oldEndIndex: nFrom + (oTo - oFrom), newEndIndex: nTo,
      startPosition, newEndPosition: pt(newDoc, nTo),
      oldEndPosition: {
        row: startPosition.row + oE.row - oS.row,
        column: oE.row == oS.row ? startPosition.column + oE.column - oS.column : oE.column,
      },
    })
  }
  return edits
}

class TreeSitterParser extends Parser {
  constructor(tsLanguage, highlights) {
    super()
    this.ts = new TSParser()
    this.ts.setLanguage(tsLanguage)
    this.query = new Query(tsLanguage, highlights)
    this.captureIndex = new Map(this.query.captureNames.map((name, i) => [name, i]))
    this.captureRules = this.query.captureNames.map(ruleFor)
    this.types = []
    for (let id = 0; id < tsLanguage.nodeTypeCount; id++) {
      const name = tsLanguage.nodeTypeForId(id) ?? ""
      this.types.push(NodeType.define({ id, name, top: name == "compilation_unit" }))
    }
    // tree-sitter's ERROR symbol is 0xFFFF, outside the language's type table
    this.errorID = this.types.length
    this.types.push(NodeType.define({ id: this.errorID, name: "ERROR", error: true }))
    this.topID = this.types.find(n => n.isTop).id
    this.captureTypes = new Map() // symbol * captureCount + capture -> NodeType
    this.typeRules = new Map() // captured type id -> highlight rule
    this.props = [
      NodeProp.closedBy.add(type => brackets[type.name] && [brackets[type.name]]),
      NodeProp.openedBy.add(type => closers[type.name] && [closers[type.name]]),
      languageDataProp.add(type => type.isTop ? languageData : undefined),
      foldNodeProp.add(() => foldNode),
      indentNodeProp.add(type => blockTypes.has(type.name) ? indentBlock : undefined),
      styleTags({ ERROR: t.invalid }),
      type => this.typeRules.has(type.id) ? [ruleProp, this.typeRules.get(type.id)] : null,
    ]
    this.nodeSet = new NodeSet(this.types).extend(...this.props)
    this.last = null // { tree, tsTree, doc, subtrees: Map<tsNodeId, Tree> }
  }

  // Lezer node type for a tree-sitter node type captured by the highlight query.
  captureType(symbol, capture) {
    const key = symbol * this.captureRules.length + capture
    let type = this.captureTypes.get(key)
    if (!type) {
      type = NodeType.define({ id: this.types.length, name: this.types[symbol].name })
      this.types.push(type)
      this.captureTypes.set(key, type)
      this.typeRules.set(type.id, this.captureRules[capture])
      this.nodeSet = new NodeSet(this.types).extend(...this.props)
    }
    return type.id
  }

  createParse(input, fragments) {
    return {
      parsedPos: 0, stoppedAt: null, stopAt() {},
      advance: () => {
        const doc = input.doc, text = doc ? doc.toString() : input.read(0, input.length)
        const prev = doc && this.last && fragments.length && fragments[0].tree == this.last.tree ? this.last : null
        let oldTs = null
        if (prev) {
          oldTs = prev.tsTree
          for (const e of fragmentsToEdits(fragments, prev.doc, doc)) oldTs.edit(e)
        } else if (this.last) this.last.tsTree.delete()
        const tsTree = this.ts.parse(text, oldTs)
        oldTs?.delete()
        const { tree, subtrees } = this.convert(tsTree, prev?.subtrees)
        this.last = { tree, tsTree, doc, subtrees }
        this.parsedPos = input.length
        return tree
      },
    }
  }

  convert(tsTree, prevSubtrees) {
    const cur = tsTree.walk(), errorID = this.errorID
    const buf = [], reused = [], subtrees = new Map()
    let captures // tree-sitter node id -> capture index, for the top-level node being built
    const typeId = () => {
      const symbol = cur.nodeTypeId < errorID ? cur.nodeTypeId : errorID
      const capture = captures.get(cur.nodeId)
      return capture == null ? symbol : this.captureType(symbol, capture)
    }
    const visit = out => { // postfix: children, then [type, start, end, size]
      const start = out.length
      if (cur.gotoFirstChild()) {
        do visit(out); while (cur.gotoNextSibling())
        cur.gotoParent()
      }
      out.push(typeId(), cur.startIndex, cur.endIndex, out.length - start + 4)
    }
    if (cur.gotoFirstChild()) {
      do {
        const node = cur.currentNode, from = cur.startIndex, to = cur.endIndex
        let sub = prevSubtrees?.get(node.id)
        if (!sub) {
          captures = new Map() // later patterns win, as in nvim-treesitter
          for (const c of this.query.captures(node)) {
            const i = this.captureIndex.get(c.name)
            if (this.captureRules[i]) captures.set(c.node.id, i)
          }
          const b = [], topID = typeId()
          if (cur.gotoFirstChild()) {
            do visit(b); while (cur.gotoNextSibling())
            cur.gotoParent()
          }
          sub = Tree.build({ buffer: b, nodeSet: this.nodeSet, topID, start: from, length: to - from })
        }
        subtrees.set(node.id, sub)
        buf.push(reused.length, from, to, -1)
        reused.push(sub)
      } while (cur.gotoNextSibling())
    }
    cur.delete()
    const tree = Tree.build({ buffer: buf, nodeSet: this.nodeSet, reused, topID: this.topID, length: tsTree.rootNode.endIndex })
    return { tree, subtrees }
  }
}

export function treeSitterLanguage(tsLanguage, highlights) {
  const parser = new TreeSitterParser(tsLanguage, highlights)
  return new LanguageSupport(new Language(languageData, parser, [foldIndented, indentScala], "scala"))
}

// Patterns missing from, or stale in, the grammar's highlights.scm (later patterns win).
// Since tree-sitter-scala 0.24 import paths are flat, repeated `path:` children with no
// `stable_identifier`; the query's field-based pattern only matches the first segment.
export const scalaExtraHighlights = `
(package_identifier (identifier) @namespace)
(import_declaration (identifier) @namespace)
(export_declaration (identifier) @namespace)
(namespace_selectors (identifier) @namespace)
(as_renamed_identifier (identifier) @namespace)
(arrow_renamed_identifier (identifier) @namespace)
`

export async function scalaTreeSitter() {
  await TSParser.init({ locateFile: () => tsWasm })
  return treeSitterLanguage(await TSLanguage.load(scalaWasm), scalaHighlights + scalaExtraHighlights)
}
