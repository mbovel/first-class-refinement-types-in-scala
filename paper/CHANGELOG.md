# Changelog

Main changes to the paper since the OOPSLA 2026 submission (tag
`oopsla-2026-initial`). A visual diff can be generated with
`./make-diff.sh`.

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
- **Typos and smaller fixes** addressing individual reviewer comments.
