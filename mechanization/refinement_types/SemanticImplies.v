(** * Semantic Implication (Figure 8)

    The judgment Γ ⊨ p₁ ⇒ p₂, used by the subtyping rule S-Refine to
    compare refinement predicates. It has no syntactic counterpart: in the
    implementation, predicate entailment is delegated to the solver. *)

Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.Wf.

(** Semantic implication: in all well-formed environments, if [p1] evaluates
    to true then [p2] evaluates to true (both read partially: a diverging
    predicate counts as true). *)
Definition sem_implies (tbounds: TBounds) (tenv: list Ty) (facts: list ((nat * Term) * (nat * Term))) (p1 p2: Term) : Prop :=
  forall tvars venv,
    wf_env tvars tenv venv ->
    wf_benv tvars tbounds venv ->
    wf_facts venv facts ->
    eval_to_true venv p1 ->
    eval_to_true venv p2.
