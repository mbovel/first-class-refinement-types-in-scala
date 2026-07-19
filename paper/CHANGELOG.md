# Changelog

Main changes to the paper since the OOPSLA 2026 submission (tag
`oopsla-2026-initial`). A visual diff can be generated with
`./make-diff.sh`.

## Done

- **Non-terminating predicates: properties established formally (§2.3).**
  (8b60bad) Promoted the non-termination discussion to its own
  subsection and stated the metatheoretic properties of the design as lemmas,
  proved in the Rocq mechanization (`ExamplesPartialSoundness.v`): entailment
  `Γ ⊨ t && true ⇒ t` holds for arbitrary, possibly diverging `t`; entailment
  `Γ ⊨ t && false ⇒ false` fails for diverging `t` and holds when `t`
  terminates; and a diverging predicate is vacuous — `{x: A | diverge}`,
  `{x: A | true}`, and `A` are mutual subtypes, and no converging term has type
  `{x: A | false}`. Predicates are now explicitly framed as operational,
  never translated into a classical logic.
- **Clarified the depth-bounded interpreter (§3.2).** (b0bc60f) The fuel
  parameter bounds the *depth* of evaluation, not the total number of steps:
  when evaluating an application, the function, the argument, and the body are
  all evaluated with the same, decremented fuel. The previous prose incorrectly
  suggested that fuel is decremented only for the body, and the listing did not
  decrement the fuel at all.
- **Skolem terms instead of skolem types (§4.2).** (4bb4920) An implementation
  detail, unrelated to the reviews and largely orthogonal to the subject of the
  paper: the implementation no longer reuses Scala's built-in skolem types; it
  now uses its own custom skolem terms in predicates. The "Hoisting and
  skolems" section was reworded accordingly.
- **Fixed a miscitation in related work (§5).** (37883cb) Paraskevopoulou et al.
  use an interpreter-based approach with step-indexed logical relations for
  multi-pass compiler verification; the previous text misattributed the
  combination of definitional interpreters with semantic typing to them.
- **Named variables in the metatheory lemmas (§3.6).** The weakening,
  substitution, and avoidance lemmas were previously stated in de Bruijn style
  to match the mechanization, an unannounced notation shift the reviewers found
  jarring. They are now stated with named variables like the rest of the paper:
  explicit shifts `A[↑]` become freshness side conditions `x ∉ FV(A)`, and
  environment extension `v, ρ` becomes `ρ[x ↦ v]`. A notation remark records
  that the mechanization states these lemmas in de Bruijn form.
- **Impact on code that does not use the feature (§4.4).** Added a paragraph
  reporting that the full Dotty CI passes with the feature enabled — the Scala
  compiler itself (~200K LOC), its ~10K compilation tests (~300K LOC), and a
  community build of 50 open-source projects (~700K LOC) — and that the
  official Scala compiler benchmark suite shows no noticeable regression,
  addressing reviewer A's backward-compatibility and performance question.
- **Non-terminating predicates highlighted as a key contribution (§1).**
  As requested by the metareview: the design bullet of the Contributions
  list now names the partial-correctness semantics with no termination
  checking as a distinctive design choice, the soundness bullet states that
  soundness needs no termination assumptions and points to the §2.3 lemmas
  proved in Rocq, and the abstract gained a sentence. The bullets keep
  their one-to-one correspondence with sections 2--4.
- **Typos and smaller fixes** addressing individual reviewer comments.

## TODO

Revisions promised in the OOPSLA response or requested by the metareview
that are not yet in the paper:

- **Add the four promised related-work references.** Flux, Thrust, and the
  refined library are in, but these are absent from both `paper.tex` and
  `references.bib`:
  - Generic Refinement Types (POPL 2025)
  - Checker Framework / pluggable types (ICSE SEIP 2011)
  - Lightweight verification of array indexing (ISSTA 2018)
  - Combining expressive type systems and deductive verification
    (OOPSLA 2021)
- **Rename and introduce the δ function in E-BinOp.** The response promised
  "We will change the name of the delta function and introduce it".
  `fig-eval.tex` still uses `\delta(op, v_a, v_b)`, it is never introduced
  in the prose, and it clashes with the δ used for type-variable
  assignments in §3.5.
- **Remove "qualified type" leftovers.** The response promised "refinement
  type" consistently. Two remain in the §4 implementation list: the
  *Adaptation* item ("when the expected type is a qualified type") and
  *Argument hoisting* ("contains qualified types"). (The occurrence quoting
  Schmid and Kunčak is fine.)
- **Fix reviewer B's L108-109 comma splice**, marked "Fixed, thanks" in the
  response but not actually fixed: "it requires no additional type system
  mechanism, it follows directly from subtyping" should use a semicolon.

Borderline / soft promises, currently unaddressed:

- **Dafny "subset types" clarification** — the response answered reviewer B,
  but the paper still calls Dafny a refinement-type system with only the
  leino2010 citation. A footnote or the subset-types citation would preempt
  the complaint.
- **Design-choice motivations in §3** — offered conditionally ("Are there
  specific rules you would like us to motivate?"). The "bad bounds"
  motivation exists but only in related work (§5), not in §3 where
  reviewer A wanted the why.
- **"Pre-installs a provisional type"** — the response offered to expand;
  the sentence is still one line.
