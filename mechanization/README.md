# Semantic Types Mechanization

- [`refinement_types/`](refinement_types/): mechanization of System F with refinement and dependent function types in Rocq, using a definitional interpreter and semantic types.

## File overview

Where a definition or theorem corresponds to a numbered figure or lemma of
the paper, the coqdoc heading in the `.v` file cites it (e.g. `Interpretation
(Figure 8)`, `Monotonicity (Lemma 3.9)`).

| File | Contents | Paper |
| --- | --- | --- |
| `Syntax.v` | Types, terms, values | Figure 5 |
| `Eval.v` | Fuel-bounded definitional interpreter | Figures 6, 7 |
| `Subst.v`, `SubstLemmas.v`, `SubstExamples.v` | De Bruijn renaming and substitution, equational theory, unit tests | §3.1 |
| `EvalLemmas.v` | Fuel monotonicity, loop invariants | §3.2 |
| `EvalShiftLemmas.v` | Evaluation weakening | Lemma 3.7 |
| `EvalSubstLemmas.v` | Evaluation substitution | §3.6 |
| `EvalTypeErasure.v` | Evaluation commutes with type erasure | §3.2 |
| `Interp.v` | Value and term interpretations V⟦·⟧ and E⟦·⟧ | Figure 8 |
| `InterpShiftLemmas.v` | Interpretation weakening | Lemmas 3.3, 3.5 |
| `InterpSubstLemmas.v` | Interpretation substitution | Lemmas 3.4, 3.6 |
| `Wf.v`, `WfLemmas.v` | Well-formed environments wf(δ, Γ, ρ) | Figure 8 |
| `Positivity.v` | Strict positivity check | Figure 11 |
| `PositivityLemmas.v` | Monotonicity and distribution | Lemmas 3.9, 3.10 |
| `Avoid.v`, `AvoidLemmas.v` | Avoidance and its soundness | §3.4, Lemma 3.8 |
| `FirstOrder.v`, `FirstOrderLemmas.v` | First-order types, binop compatibility | §3.4 |
| `SemanticImplies.v` | Semantic implication judgment | Figure 8 |
| `SemanticTyping.v` | Semantic typing judgment and rule lemmas | Figures 8, 9 |
| `SemanticSubtyping.v` | Semantic subtyping judgment and rule lemmas | Figures 8, 10 |
| `SyntacticTyping.v`, `SyntacticSubtyping.v` | Inductive syntactic judgments | Figures 9, 10 |
| `Adequacy.v` | Syntactic judgments imply semantic ones | Theorems 3.1, 3.2 |
| `AlgorithmicTyping.v` | Computable type checker (test only) | — |
| `Examples.v` | `maximum` example | — |
| `ExamplesCollect.v` | `collect` example | Figure 4 |
| `ExamplesPartialSoundness.v` | Divergent-predicate lemmas | Lemmas 2.1–2.3 |
| `ListLemmas.v`, `Tactics.v` | Generic helpers | — |

Note: the paper presents singleton base types `True`/`False` (with `Bool`
recovered as `True ∨ False`); the mechanization uses a single `Bool` type.


## Build

```bash
make
```

## Docker

The top-level artifact image includes Rocq 9.2. From the repository root:

```bash
docker build -t refinement-artifact .
docker run --rm refinement-artifact mechanization
```
