From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
From Stdlib Require Import ZArith.BinInt.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Tactics.

(** ** Fuel monotonicity for run_loop *)
Lemma run_loop_mono : forall step1 step2 n1 n2 va r,
  n1 <= n2 ->
  (forall v r, step1 v = Some r -> step2 v = Some r) ->
  run_loop step1 n1 va = Some r ->
  run_loop step2 n2 va = Some r.
Proof.
  intros step1 step2 n1.
  induction n1; intros; try discriminate.
  destruct n2; [lia|].
  simpl in *.
  destruct (step1 va) as [[v|]|] eqn:Hs; try discriminate.
  - assert (Hs2 := H0 _ _ Hs). rewrite Hs2.
    destruct v; try (exact H1);
      try (eapply IHn1; [lia | eauto | eauto]).
  - assert (Hs2 := H0 _ _ Hs). rewrite Hs2. exact H1.
Qed.

(** ** Type preservation for run_loop *)
Lemma run_loop_typed : forall step n va (A B : Value -> Prop),
  A va ->
  (forall v, A v -> forall r, step v = Some r ->
    exists w, r = Some w /\
      match w with
      | vinl u => A u
      | vinr u => B u
      | _ => False
      end) ->
  forall r, run_loop step n va = Some r ->
  exists v, r = Some v /\ B v.
Proof.
  intros step n.
  induction n; intros va A B HAva Hstep r Hloop.
  - discriminate.
  - simpl in Hloop.
    destruct (step va) as [[w|]|] eqn:Hs; try discriminate.
    + destruct (Hstep va HAva _ Hs) as [w' [Hw' HwP]].
      injection Hw' as <-.
      destruct w;
        try (simpl in HwP; contradiction).
      (* vinl case - continue *)
      * eapply IHn; [exact HwP | exact Hstep | exact Hloop].
      (* vinr case - break *)
      * injection Hloop as <-.
        eexists. split; [reflexivity | exact HwP].
    + injection Hloop as <-.
      destruct (Hstep va HAva _ Hs) as [w' [Hw' _]]. discriminate.
Qed.

(** ** Fuel monotonicity *)
Lemma eval_fuel_mono: forall fuel1 fuel2 env t r,
  fuel1 <= fuel2 ->
  eval fuel1 env t = Some r ->
  eval fuel2 env t = Some r.
Proof.
  induction fuel1; intros; try discriminate.
  destruct fuel2; try lia.
  assert (fuel1 <= fuel2) by lia.
  destruct t; auto; simpl in *;
    try (repeat (repeat prune_branches; erewrite IHfuel1; eauto); fail).
  (* tloop *)
  destruct (eval fuel1 env t1) as [[va|]|] eqn:Ha.
  -- assert (Ha2 : eval fuel2 env t1 = Some (Some va)) by (eapply IHfuel1; eauto).
     rewrite Ha2.
     eapply run_loop_mono; [eauto | | eauto].
     intros. eapply IHfuel1; eauto.
  -- assert (Ha2 : eval fuel2 env t1 = Some None) by (eapply IHfuel1; eauto).
     rewrite Ha2. exact H0.
  -- discriminate.
Qed.

(** ** Evaluation of binary operations *)

(** General tbin_op evaluation: if both sides evaluate and eval_bin_op succeeds. *)
Lemma eval_tbin_op: forall fuel1 fuel2 env op a b va vb v,
  eval fuel1 env a = Some (Some va) ->
  eval fuel2 env b = Some (Some vb) ->
  eval_bin_op op va vb = Some v ->
  eval (S (fuel1 + fuel2)) env (tbin_op op a b) = Some (Some v).
Proof.
  intros. simpl.
  rewrite eval_fuel_mono with (fuel1 := fuel1) (r := Some va); try lia; auto.
  rewrite eval_fuel_mono with (fuel1 := fuel2) (r := Some vb); try lia; auto.
  rewrite H1. reflexivity.
Qed.

(** Equality via eval_bin_op is defined on all pairs of first-order values. *)
Lemma eval_bin_op_eq_fo_defined: forall va vb,
  fo_val va -> fo_val vb ->
  exists r, eval_bin_op OpEq va vb = Some r.
Proof.
  intros va vb [-> | [[b1 ->] | [z1 ->]]] [-> | [[b2 ->] | [z2 ->]]];
  simpl; eauto.
Qed.

(** Equality is reflexive on first-order values. *)
Lemma eval_bin_op_eq_refl: forall v, fo_val v -> eval_bin_op OpEq v v = Some (vbool true).
Proof.
  intros v [Hunit | [Hbool | Hint32]].
  - subst. reflexivity.
  - destruct Hbool as [b ->]. simpl. rewrite Bool.eqb_reflx. reflexivity.
  - destruct Hint32 as [z ->]. simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** eval_bin_op is defined on compatible value pairs. *)
Lemma eval_bin_op_defined: forall op va vb,
  bin_op_val_pair_compat op va vb ->
  exists r, eval_bin_op op va vb = Some r.
Proof.
  intros op va vb Hcompat.
  destruct op; simpl in *;
    first [ destruct Hcompat as [z1 [z2 [-> ->]]];
            simpl; eauto
          | destruct Hcompat as [b1 [b2 [-> ->]]];
            simpl; eauto
          | destruct Hcompat as [Hva Hvb];
            destruct Hva as [-> | [[b1 ->] | [z1 ->]]];
            destruct Hvb as [-> | [[b2 ->] | [z2 ->]]];
            simpl; eauto ].
Qed.
