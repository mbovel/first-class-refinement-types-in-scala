(** * Examples: partial correctness and divergent predicates

    These examples support the response to reviewers about the soundness of
    accepting non-terminating refinement predicates.

    The key observations are:
    - A refinement [{x: A | false}] is uninhabited (equivalent to [Bot]).
    - A refinement [{x: A | true}] is equivalent to its base type [A].
    - A refinement with a diverging predicate is *vacuous*: it adds no
      constraint, so [{Unit | diverge}] is equivalent to [Unit] (and thus to
      [{Unit | true}]).
    - However, a diverging predicate is *not* the same as a false predicate:
      [{Unit | diverge}] is inhabited but [{Unit | false}] is not.
    - This holds even when the diverging predicate appears inside a larger
      expression that would otherwise be false, e.g. [diverge() && false]. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.Wf.
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

(** ** 3a. [{Unit | diverge}] is *not* a semantic subtype of [{Unit | false}].

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

(** ** 3b. [{Unit | diverge && false}] is *not* a subtype of [{Unit | false}].

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
