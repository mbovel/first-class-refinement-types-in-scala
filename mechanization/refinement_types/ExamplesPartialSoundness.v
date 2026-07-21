(** * Partial Correctness and Divergent Predicates (§2.3, Lemmas 2.1–2.3)

    These theorems establish the metatheoretic properties of accepting
    non-terminating refinement predicates under the partial-correctness
    semantics. They include the lemmas of §2.3 of the paper:
    - Lemma 2.1 (And-True): [sem_implies_and_true]
    - Lemma 2.2 (And-False): [sem_implies_and_false_terminating], with
      [diverge_and_false_not_implies_false] showing that its termination
      hypothesis is necessary
    - Lemma 2.3 (diverging predicates are vacuous):
      [refine_diverge_eq_refine_true] and [refine_true_eq_base] (part 1),
      [no_converging_term_has_refine_false] (part 2), and
      [diverge_not_sub_false] (part 3)

    The key observations are:
    - A refinement [{x: A | false}] is uninhabited (equivalent to [Bot]).
    - A refinement [{x: A | true}] is equivalent to its base type [A].
    - A refinement with a diverging predicate is *vacuous*: it adds no
      constraint, so [{x: A | diverge}] is equivalent to [{x: A | true}]
      (and thus to [A]), for any [A].
    - However, a diverging predicate is *not* the same as a false predicate:
      [{x: A | diverge}] is inhabited but [{x: A | false}] is not.
    - This holds even when the diverging predicate appears inside a larger
      expression that would otherwise be false, e.g. [diverge() && false].
    - Entailment rules differ in whether they need termination:
      [Γ ⊨ t && true ⟹ t] holds for arbitrary (possibly diverging) [t],
      whereas [Γ ⊨ t && false ⟹ false] fails for diverging [t] and is
      recovered when [t] terminates.

    In short: a diverging predicate cannot be used to prove [false]. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.SemanticImplies.
Require Import RefinementTypes.SemanticSubtyping.
Require Import RefinementTypes.SemanticTyping.

(** [tdiverge] never reduces to a value, regardless of fuel or environment. *)
Lemma eval_tdiverge : forall fuel env,
  eval fuel env tdiverge = None.
Proof.
  intros [|fuel] env; reflexivity.
Qed.

(** ** 0a. [Bot] and [{T | false}] have the same interpretation, for any [T].

    A refinement whose predicate evaluates to [false] is uninhabited, just
    like [Bot] — regardless of the base type. *)

Theorem bot_eq_refine_false :
  forall T tvars venv v,
    interp tvars venv TBot v <-> interp tvars venv (TRefine T (tbool false)) v.
Proof.
  intros T tvars venv v. split.
  - (* Bot is empty, so the implication is vacuous. *)
    intros [].
  - (* If v inhabits {T | false} then the predicate [false] evaluates to
       [true] at fuel 1, which is impossible. *)
    intros [_ Heval].
    specialize (Heval 1 (Some (vbool false)) eq_refl).
    destruct Heval as [v' [Heq Htrue]]. injection Heq as <-. discriminate.
Qed.

(** ** 0b. [Unit] and [{Unit | true}] have the same interpretation.

    A trivially-true predicate adds no constraint, so the refinement
    collapses to its base type. *)

Theorem unit_eq_unit_with_true :
  forall tvars venv v,
    interp tvars venv TUnit v <-> interp tvars venv (TRefine TUnit (tbool true)) v.
Proof.
  intros tvars venv v. split.
  - (* If v is unit, the predicate [true] evaluates to [true] under any
       nonzero fuel, so the refinement holds. *)
    intros Hunit. split; [exact Hunit|].
    intros [|fuel] r Heval; [discriminate|].
    simpl in Heval. injection Heval as <-.
    exists (vbool true). split; reflexivity.
  - (* The refinement implies the base type. *)
    intros [Hunit _]. exact Hunit.
Qed.

(** ** 1a. No value inhabits [Bot]. *)

Theorem no_value_in_bot :
  forall tvars venv v, ~ interp tvars venv TBot v.
Proof.
  intros tvars venv v [].
Qed.

(** ** 1b. No converging term has type [Bot].

    If [t] evaluates to a value [v] in any well-formed environment, then [t]
    cannot be semantically typed at [Bot]. *)

Theorem no_converging_term_has_bot :
  forall tbounds tenv facts t tvars venv fuel v,
    wf_env tvars tenv venv ->
    wf_benv tvars tbounds venv ->
    wf_facts venv facts ->
    eval fuel venv t = Some (Some v) ->
    ~ sem_typed tbounds tenv facts t TBot.
Proof.
  intros * Hwf Hbwf Hfwf Heval Htyped.
  specialize (Htyped tvars venv Hwf Hbwf Hfwf fuel (Some v) Heval).
  destruct Htyped as [v' [_ []]].
Qed.

(** ** 2. [{Unit | true}] and [{Unit | diverge}] have the same interpretation.

    A diverging predicate is *vacuous*: the partial-correctness reading
    ([if] the predicate terminates, [then] it returns [true]) is trivially
    satisfied. So [diverge] and [true] are interchangeable as refinement
    predicates. *)

Theorem unit_with_true_eq_unit_with_diverge :
  forall tvars venv v,
    interp tvars venv (TRefine TUnit (tbool true)) v <->
    interp tvars venv (TRefine TUnit tdiverge) v.
Proof.
  intros tvars venv v. split.
  - (* From {Unit | true} to {Unit | diverge}: the diverge predicate is
       vacuously true because [eval fuel _ tdiverge] is never [Some _]. *)
    intros [Hunit _]. split; [exact Hunit|].
    intros [|fuel] r Heval; discriminate.
  - (* From {Unit | diverge} to {Unit | true}: re-prove the [true] side. *)
    intros [Hunit _]. split; [exact Hunit|].
    intros [|fuel] r Heval; [discriminate|].
    simpl in Heval. injection Heval as <-.
    exists (vbool true). split; reflexivity.
Qed.

(** ** 3a. [{Unit | diverge}] is not a semantic subtype of [{Unit | false}]
    (Lemma 2.3, part 3).

    [vunit] inhabits the first but not the second, so the system is not
    degenerate: a diverging predicate is not equivalent to [false]. *)

Theorem diverge_not_sub_false :
  ~ sem_subtype [] [] [] (TRefine TUnit tdiverge) (TRefine TUnit (tbool false)).
Proof.
  intros Hsub.
  specialize (Hsub [] [] I I (Forall_nil _) vunit).
  destruct Hsub as [_ Heval].
  - (* [vunit] inhabits {Unit | diverge}: it has base type [Unit] and the
       diverging predicate vacuously satisfies eval_to_true. *)
    split; [reflexivity|].
    intros [|fuel] r Hev; discriminate.
  - (* But the [false] predicate evaluates to [false], contradicting
       eval_to_true. *)
    specialize (Heval 1 (Some (vbool false)) eq_refl).
    destruct Heval as [v' [Heq Htrue]]. injection Heq as <-. discriminate.
Qed.

(** ** 3b. [{Unit | diverge && false}] is not a subtype of [{Unit | false}].

    Strict left-to-right evaluation means [diverge && false] still diverges:
    the outer [false] is unreachable. So the refinement is vacuously
    satisfied, and [vunit] inhabits it even though the conjunction "would
    have been" [false] under a more eager semantics. *)

Theorem diverge_and_false_not_sub_false :
  ~ sem_subtype [] [] []
      (TRefine TUnit (tbin_op OpAnd tdiverge (tbool false)))
      (TRefine TUnit (tbool false)).
Proof.
  intros Hsub.
  specialize (Hsub [] [] I I (Forall_nil _) vunit).
  destruct Hsub as [_ Heval].
  - (* [vunit] inhabits {Unit | diverge && false}: evaluation of the
       binop tries its left operand [diverge] first, which loops, so the
       whole binop diverges and the partial-correctness reading is vacuous. *)
    split; [reflexivity|].
    intros [|fuel] r Hev; [discriminate|].
    simpl in Hev. rewrite eval_tdiverge in Hev. discriminate.
  - (* But the [false] predicate evaluates to [false], contradicting
       eval_to_true. *)
    specialize (Heval 1 (Some (vbool false)) eq_refl).
    destruct Heval as [v' [Heq Htrue]]. injection Heq as <-. discriminate.
Qed.

(** ** Helper: evaluation of [t && b] in terms of the evaluation of [t].

    If [t] terminates with result [r], then [t && b] terminates at one more
    unit of fuel: with the boolean [andb r b] if [r] is a boolean value, and
    stuck otherwise. *)

Lemma eval_and_bool : forall fuel env t b r,
  eval fuel env t = Some r ->
  eval (S fuel) env (tbin_op OpAnd t (tbool b)) =
    match r with
    | Some (vbool b') => Some (Some (vbool (andb b' b)))
    | Some _ => Some None
    | None => Some None
    end.
Proof.
  intros fuel env t b r Heval.
  (* [fuel] is a variable, so [simpl] unfolds only the outer application of
     [eval] and leaves the operands' evaluations folded. *)
  simpl. rewrite Heval.
  destruct r as [va|]; [|reflexivity].
  destruct fuel as [|fuel]; [discriminate|].
  simpl. destruct va; reflexivity.
Qed.

(** ** 4. Entailment [Γ ⊨ t && true ⟹ t] holds for arbitrary [t]
    (Lemma 2.1, And-True).

    No termination assumption on [t] is needed: if [t && true] evaluates to
    [true] whenever it terminates, then so does [t]. A case analysis shows the
    two sides line up, including the vacuous case where [t] diverges (then
    [t && true] diverges too, and both sides hold vacuously). *)

Theorem sem_implies_and_true :
  forall tbounds tenv facts t,
    sem_implies tbounds tenv facts (tbin_op OpAnd t (tbool true)) t.
Proof.
  intros tbounds tenv facts t tvars venv _ _ _ Hconj fuel r Heval.
  (* Suppose [t] terminates with result [r] at some fuel. *)
  assert (Hev' := eval_and_bool _ _ _ true _ Heval).
  (* If [r] is stuck or not a boolean, [t && true] is stuck, contradicting
     the assumption that [t && true] evaluates to [true]. *)
  destruct r as [va|]; [destruct va|];
    try (destruct (Hconj _ _ Hev') as [w [Hw _]]; discriminate).
  (* If [r] is a boolean [b], then [t && true] evaluates to [b], which
     must be [true]; hence [t] evaluates to [true] as required. *)
  destruct b.
  - eexists. split; reflexivity.
  - destruct (Hconj _ _ Hev') as [w [Hw Htrue]].
    injection Hw as <-. discriminate.
Qed.

(** ** 5a. Entailment [Γ ⊨ t && false ⟹ false] fails for diverging [t].

    With [t = diverge], the left-hand side diverges, so it is vacuously true
    under the partial-correctness reading, while [false] is not. This shows
    that the termination hypothesis of Lemma 2.2 is necessary. *)

Theorem diverge_and_false_not_implies_false :
  ~ sem_implies [] [] [] (tbin_op OpAnd tdiverge (tbool false)) (tbool false).
Proof.
  intros Himp.
  (* [diverge && false] diverges, so it vacuously satisfies eval_to_true. *)
  assert (Hvac : eval_to_true [] (tbin_op OpAnd tdiverge (tbool false))).
  { intros [|fuel] r Hev; [discriminate|].
    simpl in Hev. rewrite eval_tdiverge in Hev. discriminate. }
  (* But [false] evaluates to [false], not [true]. *)
  specialize (Himp [] [] I I (Forall_nil _) Hvac 1 (Some (vbool false)) eq_refl).
  destruct Himp as [v [Heq Htrue]]. injection Heq as <-. discriminate.
Qed.

(** ** 5b. Entailment [Γ ⊨ t && false ⟹ false] holds when [t] terminates
    (Lemma 2.2, And-False).

    A term [t] semantically terminates in a context if it evaluates to a
    value in every well-formed environment. *)

Definition sem_terminates (tbounds: TBounds) (tenv: list Ty)
    (facts: list ((nat * Term) * (nat * Term))) (t: Term) : Prop :=
  forall tvars venv,
    wf_env tvars tenv venv ->
    wf_benv tvars tbounds venv ->
    wf_facts venv facts ->
    exists fuel v, eval fuel venv t = Some (Some v).

(** If [t] terminates, the entailment is recovered: [t && false] then
    evaluates to [false] (or is stuck), so its eval_to_true assumption is
    contradictory. *)

Theorem sem_implies_and_false_terminating :
  forall tbounds tenv facts t,
    sem_terminates tbounds tenv facts t ->
    sem_implies tbounds tenv facts (tbin_op OpAnd t (tbool false)) (tbool false).
Proof.
  intros tbounds tenv facts t Hterm tvars venv Henv Hbenv Hfacts Hconj.
  destruct (Hterm tvars venv Henv Hbenv Hfacts) as [fuel [v Heval]].
  exfalso.
  (* [t && false] terminates at one more unit of fuel, and its result is
     [false] (if [v] is a boolean) or stuck (otherwise), contradicting the
     assumption that it evaluates to [true]. *)
  assert (Hev' := eval_and_bool _ _ _ false _ Heval).
  destruct v;
    try (destruct (Hconj _ _ Hev') as [w [Hw _]]; discriminate).
  destruct b;
    destruct (Hconj _ _ Hev') as [w [Hw Htrue]];
    injection Hw as <-; discriminate.
Qed.

(** ** 6. [{x: A | diverge}] and [{x: A | true}] have the same interpretation,
    for any base type [A] (Lemma 2.3, part 1).

    This generalizes example 2 above: a diverging predicate is vacuous, so it
    is interchangeable with [true] as a refinement predicate. Together with
    example 7 below, this shows that allowing diverging predicates is sound
    and not degenerate: a diverging predicate cannot be used to prove
    [false]. *)

Theorem refine_diverge_eq_refine_true :
  forall A tvars venv v,
    interp tvars venv (TRefine A tdiverge) v <->
    interp tvars venv (TRefine A (tbool true)) v.
Proof.
  intros A tvars venv v. split.
  - (* From {A | diverge} to {A | true}: re-prove the [true] side. *)
    intros [HA _]. split; [exact HA|].
    intros [|fuel] r Heval; [discriminate|].
    simpl in Heval. injection Heval as <-.
    exists (vbool true). split; reflexivity.
  - (* From {A | true} to {A | diverge}: the diverging predicate is
       vacuously true because [eval fuel _ tdiverge] is never [Some _]. *)
    intros [HA _]. split; [exact HA|].
    intros [|fuel] r Heval; discriminate.
Qed.

(** As a corollary, the two types are semantic subtypes of each other
    ([<:>], two-way subtyping) in any context. *)

Corollary sem_subtype_refine_diverge_true :
  forall tbounds tenv facts A,
    sem_subtype tbounds tenv facts (TRefine A tdiverge) (TRefine A (tbool true)).
Proof.
  intros tbounds tenv facts A tvars venv _ _ _ v Hv.
  exact (proj1 (refine_diverge_eq_refine_true A tvars venv v) Hv).
Qed.

Corollary sem_subtype_refine_true_diverge :
  forall tbounds tenv facts A,
    sem_subtype tbounds tenv facts (TRefine A (tbool true)) (TRefine A tdiverge).
Proof.
  intros tbounds tenv facts A tvars venv _ _ _ v Hv.
  exact (proj2 (refine_diverge_eq_refine_true A tvars venv v) Hv).
Qed.

(** [{x: A | true}] moreover collapses to its base type [A], so
    [{x: A | diverge}] is also equivalent to [A] itself. This generalizes
    example 0b above. *)

Theorem refine_true_eq_base :
  forall A tvars venv v,
    interp tvars venv (TRefine A (tbool true)) v <-> interp tvars venv A v.
Proof.
  intros A tvars venv v. split.
  - intros [HA _]. exact HA.
  - intros HA. split; [exact HA|].
    intros [|fuel] r Heval; [discriminate|].
    simpl in Heval. injection Heval as <-.
    exists (vbool true). split; reflexivity.
Qed.

(** Hence [{x: A | true}], [{x: A | diverge}], and [A] are all semantic
    subtypes of each other, in any context. *)

Corollary sem_subtype_refine_true_base :
  forall tbounds tenv facts A,
    sem_subtype tbounds tenv facts (TRefine A (tbool true)) A.
Proof.
  intros tbounds tenv facts A tvars venv _ _ _ v Hv.
  exact (proj1 (refine_true_eq_base A tvars venv v) Hv).
Qed.

Corollary sem_subtype_base_refine_true :
  forall tbounds tenv facts A,
    sem_subtype tbounds tenv facts A (TRefine A (tbool true)).
Proof.
  intros tbounds tenv facts A tvars venv _ _ _ v Hv.
  exact (proj2 (refine_true_eq_base A tvars venv v) Hv).
Qed.

Corollary sem_subtype_refine_diverge_base :
  forall tbounds tenv facts A,
    sem_subtype tbounds tenv facts (TRefine A tdiverge) A.
Proof.
  intros tbounds tenv facts A tvars venv _ _ _ v Hv.
  apply (proj1 (refine_true_eq_base A tvars venv v)).
  exact (proj1 (refine_diverge_eq_refine_true A tvars venv v) Hv).
Qed.

Corollary sem_subtype_base_refine_diverge :
  forall tbounds tenv facts A,
    sem_subtype tbounds tenv facts A (TRefine A tdiverge).
Proof.
  intros tbounds tenv facts A tvars venv _ _ _ v Hv.
  apply (proj2 (refine_diverge_eq_refine_true A tvars venv v)).
  exact (proj2 (refine_true_eq_base A tvars venv v) Hv).
Qed.

(** ** 7. No converging term has type [{x: A | false}], for any [A]
    (Lemma 2.3, part 2).

    This generalizes example 1b above: if [t] evaluates to a value in some
    well-formed environment, then [t] cannot be semantically typed at
    [{x: A | false}]. *)

Theorem no_converging_term_has_refine_false :
  forall tbounds tenv facts t A tvars venv fuel v,
    wf_env tvars tenv venv ->
    wf_benv tvars tbounds venv ->
    wf_facts venv facts ->
    eval fuel venv t = Some (Some v) ->
    ~ sem_typed tbounds tenv facts t (TRefine A (tbool false)).
Proof.
  intros * Henv Hbenv Hfacts Heval Htyped.
  specialize (Htyped tvars venv Henv Hbenv Hfacts fuel (Some v) Heval).
  destruct Htyped as [v' [Heq [_ Hp]]].
  (* The value [v] would have to satisfy the [false] predicate, which
     evaluates to [false], contradicting eval_to_true. *)
  specialize (Hp 1 (Some (vbool false)) eq_refl).
  destruct Hp as [w [Hw Htrue]]. injection Hw as <-. discriminate.
Qed.
