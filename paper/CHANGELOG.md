# Changelog

This document summarizes the changes to the paper since the OOPSLA 2026
submission. The revision addresses the two central concerns of the
metareview. First, the treatment of non-terminating predicates is now
highlighted as a key contribution (§1), and the claims made in our
response are incorporated into the paper as formal lemmas, proved in the
Rocq mechanization (§2.3). Second, the paper now states explicitly that
the formalized calculus is pure (abstract, §1), and discusses the
integration with Stateful Capabilities and related capture-checking
extensions as future work (§2.2, §5). Beyond these, we strengthened the
compilation-overhead evaluation (a more rigorous protocol, confidence
intervals, a corrected description of Schmid's system) and addressed the
remaining individual reviewer comments. The full list of changes
follows, ordered by paper section:

- **Non-terminating predicates highlighted as a key contribution (§1).**
  As requested by the metareview: the design bullet of the Contributions
  list now names the partial-correctness semantics with no termination
  checking as a distinctive design choice.
- **Pure-calculus limitation stated explicitly; path to purity checking
  expanded (§1, §2.2).** As requested by the metareview: the abstract and
  the soundness contribution now call the formalized calculus "core,
  *pure*"; §2.2 defines predicate purity precisely (deterministic and
  side-effect-free) and flags the unenforced purity of called functions
  as an unsafe default. A new paragraph presents capture checking and its
  extensions — Stateful Capabilities, separation checking, and safe
  mode — as a concrete path to enforcing purity, and sketches how
  separation checking could soundly invalidate refinement facts under
  mutation; these integrations are left as future work.
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
- **Clarified the depth-bounded interpreter (§3.2).** The fuel
  parameter bounds the *depth* of evaluation, not the total number of steps:
  when evaluating an application, the function, the argument, and the body are
  all evaluated with the same, decremented fuel. The previous prose incorrectly
  suggested that fuel is decremented only for the body, and the listing did not
  decrement the fuel at all.
- **Renamed and introduced the E-BinOp operation function (§3.2).** The
  former δ (which clashed with the type-variable assignment δ of §3.5) is
  now `evalop`, mirroring `eval_bin_op` in the mechanization, and the
  operational-semantics prose introduces it as the partial function
  interpreting primitive operations, undefined (stuck) on ill-typed
  operands.
- **Named variables in the metatheory lemmas (§3.6).** The weakening,
  substitution, and avoidance lemmas were previously stated in de Bruijn style
  to match the mechanization, an unannounced notation shift the reviewers found
  jarring. They are now stated with named variables like the rest of the paper:
  explicit shifts `A[↑]` become freshness side conditions `x ∉ FV(A)`, and
  environment extension `v, ρ` becomes `ρ[x ↦ v]`. A notation remark records
  that the mechanization states these lemmas in de Bruijn form.
- **Skolem terms instead of skolem types (§4.2).** An implementation
  detail, unrelated to the reviews and largely orthogonal to the subject of the
  paper: the implementation no longer reuses Scala's built-in skolem types; it
  now uses its own custom skolem terms in predicates. The "Hoisting and
  skolems" section was reworded accordingly.
- **Reworked the compilation-overhead evaluation (§4.4).** The benchmarks
  were re-run with a more rigorous protocol, as promised in the
  submission's note to reviewers: 150 warm-up and 20 measurement
  iterations per JVM (previously 30 and 10), and the whole experiment
  repeated in 10 independent runs. The table now reports means with 95%
  confidence intervals (Student's t) and the absolute overhead Δ of
  checking over each system's own baseline. The methodology paragraph was
  rewritten to match, and the results paragraph now quantifies the
  conclusion: 0–12% overhead for our system, consistently less than
  Schmid's system (20–38%) and Stainless (at least 56%).
- **Impact on code that does not use the feature (§4.4).** Added a paragraph
  reporting that the full Dotty CI passes with the feature enabled — the Scala
  compiler itself (~200K LOC), its ~10K compilation tests (~300K LOC), and a
  community build of 50 open-source projects (~700K LOC) — and that the
  official Scala compiler benchmark suite stays within a 4% slowdown,
  addressing reviewer A's backward-compatibility and performance question.
- **Corrected the description of Schmid's system (§1, §4.4).** The previous
  text understated its capabilities, claiming refinements were limited to
  `Int` and could not apply to class-typed values. Schmid's system in fact
  supports qualifiers on base types and on classes, including invariants
  over stable constructor fields — our `matrixDims` and `postuple` ports
  exercise exactly this. The comparison now focuses on the real
  difference: qualifier inference runs in a separate phase, so qualified
  type arguments must be written explicitly and refinements do not
  participate in type-argument inference.
- **Fixed a miscitation in related work (§5).** Paraskevopoulou et al.
  use an interpreter-based approach with step-indexed logical relations for
  multi-pass compiler verification; the previous text misattributed the
  combination of definitional interpreters with semantic typing to them.
- **Expanded the Liquid Haskell comparison (§5).** Now covers three axes —
  separate plugin vs. in-compiler refinements, per-function termination
  obligations vs. solver-local ones, and SMT over decidable theories vs.
  e-graphs with normalization — noting that the recent PLEX extension
  (Ferrarini et al., 2026) adds exactly such normalization to Liquid
  Haskell's Proof by Logical Evaluation layer.
- **Reworked the passage on refinement types and mutation (§5).** It now
  opens with the invalidation problem (invariant vs. flow-sensitive
  refinements of mutable locations, under aliasing), presents each Rust
  system as an answer to it, adds the promised Generic Refinement Types
  reference (Lehmann et al., 2025), and links the separation-checking
  sketch of §2.2.
- **Added a *Pluggable type systems* paragraph (§5)** with the remaining
  promised references: the Checker Framework (Dietl et al., 2011) — same
  goal as refinement types, same separate-phase architecture — its
  application to array-indexing verification (Kellogg et al., 2018), and
  its combination with deductive verification (Lanzinger et al., 2021).
- **Typos and smaller fixes** addressing individual reviewer comments.
