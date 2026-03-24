From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Tactics.
Require Import RefinementTypes.EvalShiftLemmas.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.EvalTypeErasure.

(** ** eval_to_true is invariant when type erasure is preserved *)

Lemma eval_to_true_erase_eq : forall venv t1 t2,
  erase_ty_in_tm t1 = erase_ty_in_tm t2 ->
  eval_to_true venv t1 <-> eval_to_true venv t2.
Proof.
  intros venv t1 t2 Herase_eq.
  unfold eval_to_true, term_has_semtype.
  assert (Herase : forall fuel,
    oov_map erase_ty_in_val (eval fuel venv t1) =
    oov_map erase_ty_in_val (eval fuel venv t2)).
  { intro fuel. rewrite eval_erase_ty, eval_erase_ty, Herase_eq. reflexivity. }
  enough (Hdir : forall ta tb,
    (forall fuel, oov_map erase_ty_in_val (eval fuel venv ta) =
                  oov_map erase_ty_in_val (eval fuel venv tb)) ->
    (forall fuel r, eval fuel venv ta = Some r -> exists v, r = Some v /\ v = vbool true) ->
    forall fuel r, eval fuel venv tb = Some r -> exists v, r = Some v /\ v = vbool true).
  { split.
    - apply Hdir. exact Herase.
    - apply Hdir. intro fuel. symmetry. apply Herase. }
  intros ta tb Hab Ha fuel r Heval.
  specialize (Hab fuel). rewrite Heval in Hab.
  destruct (eval fuel venv ta) as [[v'|]|] eqn:Hta; simpl in Hab.
  - destruct r as [v|]; [|discriminate].
    injection Hab as Hab.
    destruct (Ha fuel (Some v') Hta) as [w [Hw1 Hw2]].
    injection Hw1 as <-. subst v'. simpl in Hab.
    exists v. split; [reflexivity|].
    apply erase_ty_in_val_vbool_true. symmetry. exact Hab.
  - destruct (Ha fuel None Hta) as [w [Hw _]]. discriminate.
  - destruct r; discriminate.
Qed.

Lemma eval_to_true_ren_ty : forall venv t xi,
  eval_to_true venv (ren_tm xi id t) <-> eval_to_true venv t.
Proof.
  intros. apply eval_to_true_erase_eq. apply erase_ty_in_tm_ren.
Qed.

Lemma eval_to_true_subst_ty : forall venv t sigma_ty,
  eval_to_true venv (subst_tm sigma_ty tvar t) <-> eval_to_true venv t.
Proof.
  intros. apply eval_to_true_erase_eq. apply erase_ty_in_tm_subst.
Qed.

Lemma eval_to_true_subst_ty_gen : forall venv t sigma_ty sigma_tm,
  (forall n, sigma_tm n = tvar n) ->
  eval_to_true venv (subst_tm sigma_ty sigma_tm t) <-> eval_to_true venv t.
Proof.
  intros venv t sigma_ty sigma_tm Htm.
  apply eval_to_true_erase_eq. apply erase_ty_in_tm_subst_gen. exact Htm.
Qed.

(** Helper: eval_to_true is preserved by environment weakening *)
Lemma eval_to_true_shift_env : forall p venv1 venv2 venv3,
  eval_to_true (venv1 ++ venv3) p <->
  eval_to_true (venv1 ++ venv2 ++ venv3)
    (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) p).
Proof.
  intros p venv1 venv2 venv3.
  unfold eval_to_true, term_has_semtype.
  split; intros H fuel r Heval.
  - (* forward: H about small env, Heval about big env *)
    destruct (eval_shift_env_bwd fuel p venv1 venv2 venv3 _ Heval) as [r' [Hrc Hr']].
    destruct r' as [[v'|]|]; [| | inversion Hrc].
    + inversion Hrc as [| | ? ? Hvc]; subst.
      destruct (H fuel (Some v') Hr') as [w [Hw Heq]].
      inversion Hw; subst. inversion Hvc; subst.
      exists (vbool true). auto.
    + inversion Hrc; subst.
      destruct (H fuel None Hr') as [w [Hw _]]. discriminate.
  - (* backward: H about big env, Heval about small env *)
    destruct (eval_shift_env_fwd fuel p venv1 venv2 venv3 _ Heval) as [r' [Hrc Hr']].
    destruct r' as [[v'|]|]; [| | inversion Hrc].
    + inversion Hrc as [| | ? ? Hvc]; subst.
      destruct (H fuel (Some v') Hr') as [w [Hw Heq]].
      inversion Hw; subst. inversion Hvc; subst.
      exists (vbool true). auto.
    + inversion Hrc; subst.
      destruct (H fuel None Hr') as [w [Hw _]]. discriminate.
Qed.

(** ** Interpretation lemmas for term variables *)

Lemma interp_weaken_term: forall T tenv venv1 venv2 venv3,
  interp tenv (venv1 ++ venv3) T =
  interp tenv (venv1 ++ venv2 ++ venv3)
    (subst_ty TVar (upn_tm (length venv1) (tm_shift (length venv2))) T).
Proof.
  induction T; intros tenv venv1 venv2 venv3; simpl; try reflexivity.
  - (* TFun *)
    assert (Hbinder: forall x,
      interp tenv (x :: venv1 ++ venv3) T2 =
      interp tenv (x :: venv1 ++ venv2 ++ venv3)
        (subst_ty (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv1) (tm_shift (length venv2)))) T2)).
    { intro x.
      replace (subst_ty (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv1) (tm_shift (length venv2)))) T2)
        with (subst_ty TVar (upn_tm (S (length venv1)) (tm_shift (length venv2))) T2)
        by (apply subst_ty_ext; [apply up_tm_ty_id | reflexivity]).
      change (S (length venv1)) with (length (x :: venv1)).
      change (x :: venv1 ++ venv3) with ((x :: venv1) ++ venv3).
      change (x :: venv1 ++ venv2 ++ venv3) with ((x :: venv1) ++ venv2 ++ venv3).
      apply (IHT2 tenv (x :: venv1) venv2 venv3). }
    unfold interp_fun.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1.
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros arg Harg.
    + rewrite <- (Hbinder arg). apply Hbody. exact Harg.
    + rewrite (Hbinder arg). apply Hbody. exact Harg.
  - (* TForall *)
    assert (Hbinder: forall A,
      interp (A :: tenv) (venv1 ++ venv3) T3 =
      interp (A :: tenv) (venv1 ++ venv2 ++ venv3)
        (subst_ty (up_ty_ty TVar) (up_ty_tm (upn_tm (length venv1) (tm_shift (length venv2)))) T3)).
    { intro A. rewrite subst_ty_up_ty_TVar_shift. apply (IHT3 (A :: tenv) venv1 venv2 venv3). }
    unfold interp_forall.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2.
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros A HL HU.
    + rewrite <- (Hbinder A). apply Hbody; assumption.
    + rewrite (Hbinder A). apply Hbody; assumption.
  - (* TRefine *)
    assert (Hpred: forall x,
      eval_to_true (x :: venv1 ++ venv3) t <->
      eval_to_true (x :: venv1 ++ venv2 ++ venv3)
        (subst_tm (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv1) (tm_shift (length venv2)))) t)).
    { intro x. rewrite subst_tm_up_tm_ty_TVar.
      replace (up_tm_tm (upn_tm (length venv1) (tm_shift (length venv2))))
        with (upn_tm (S (length venv1)) (tm_shift (length venv2)))
        by reflexivity.
      change (S (length venv1)) with (length (x :: venv1)).
      change (x :: venv1 ++ venv3) with ((x :: venv1) ++ venv3).
      change (x :: venv1 ++ venv2 ++ venv3) with ((x :: venv1) ++ venv2 ++ venv3).
      apply (eval_to_true_shift_env t (x :: venv1) venv2 venv3). }
    unfold interp_refine.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT. rewrite <- (Hpred v).
    tauto.
  - (* TSigma *)
    assert (Hbinder: forall x,
      interp tenv (x :: venv1 ++ venv3) T2 =
      interp tenv (x :: venv1 ++ venv2 ++ venv3)
        (subst_ty (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv1) (tm_shift (length venv2)))) T2)).
    { intro x.
      replace (subst_ty (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv1) (tm_shift (length venv2)))) T2)
        with (subst_ty TVar (upn_tm (S (length venv1)) (tm_shift (length venv2))) T2)
        by (apply subst_ty_ext; [apply up_tm_ty_id | reflexivity]).
      change (S (length venv1)) with (length (x :: venv1)).
      change (x :: venv1 ++ venv3) with ((x :: venv1) ++ venv3).
      change (x :: venv1 ++ venv2 ++ venv3) with ((x :: venv1) ++ venv2 ++ venv3).
      apply (IHT2 tenv (x :: venv1) venv2 venv3). }
    unfold interp_sigma.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1.
    split; intros (v1 & v2 & Heq & Ha & Hb); exists v1, v2;
      (split; [exact Heq|]; split; [exact Ha|]).
    + rewrite <- (Hbinder v1). exact Hb.
    + rewrite (Hbinder v1). exact Hb.
  - (* TSum *)
    unfold interp_sum.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2. tauto.
  - (* TOr *)
    unfold interp_or.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2. tauto.
  - (* TAnd *)
    unfold interp_and.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2. tauto.
  - (* TMuAll *)
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    split; intros Hall n; specialize (Hall n);
      revert v Hall; apply interp_mu_eq_ext; intros X w;
      rewrite subst_ty_up_ty_TVar_shift;
      rewrite (IHT (X :: tenv) venv1 venv2 venv3); tauto.
Qed.

Lemma interp_env_ren_term: forall T tenv venv v,
  interp tenv venv T = interp tenv (v::venv) (ren_ty id S T).
Proof.
  intros.
  change (v::venv) with ([] ++ [v] ++ venv).
  change venv with ([] ++ venv) at 1.
  rewrite (interp_weaken_term T tenv [] [v] venv).
  f_equal. f_equal.
  rewrite ren_subst_ty.
  apply subst_ty_ext.
  - intro n. reflexivity.
  - intro n. simpl. unfold funcomp, tm_shift. f_equal. lia.
Qed.

(** ** Interpretation lemmas for type variables *)

Lemma interp_weaken_type: forall T tenv1 tenv2 tenv3 venv,
  interp (tenv1 ++ tenv3) venv T =
  interp (tenv1 ++ tenv2 ++ tenv3) venv
    (ren_ty (fun n => if lt_dec n (length tenv1) then n else n + length tenv2) id T).
Proof.
  induction T as [i | | | | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 T3 IHT3 | T IHT t | T1 IHT1 T2 IHT2
    | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | | | T IHT];
    intros tenv1 tenv2 tenv3 venv; simpl; try reflexivity.
  - (* TVar *)
    unfold interp_var.
    destruct (lt_dec i (length tenv1)) as [Hlt | Hge].
    + rewrite nth_error_app1 by lia. rewrite nth_error_app1 by lia. reflexivity.
    + rewrite (nth_error_app2 tenv1 tenv3) by lia.
      rewrite (nth_error_app2 tenv1 (tenv2 ++ tenv3)) by lia.
      rewrite (nth_error_app2 tenv2 tenv3) by lia.
      replace (i + length tenv2 - length tenv1 - length tenv2) with (i - length tenv1) by lia.
      reflexivity.
  - (* TFun *)
    assert (Hbinder : forall arg,
      interp (tenv1 ++ tenv3) (arg :: venv) T2 =
      interp (tenv1 ++ tenv2 ++ tenv3) (arg :: venv)
        (ren_ty (fun n => if lt_dec n (length tenv1) then n else n + length tenv2) (upren id) T2)).
    { intro arg. rewrite ren_ty_upren_id. apply IHT2. }
    unfold interp_fun.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1.
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros arg Harg.
    + rewrite <- (Hbinder arg). apply Hbody. exact Harg.
    + rewrite (Hbinder arg). apply Hbody. exact Harg.
  - (* TForall *)
    assert (Hbinder : forall A,
      interp (A :: tenv1 ++ tenv3) venv T3 =
      interp (A :: tenv1 ++ tenv2 ++ tenv3) venv
        (ren_ty (upren (fun n => if lt_dec n (length tenv1) then n else n + length tenv2)) id T3)).
    { intro A.
      change (A :: tenv1 ++ tenv3) with ((A :: tenv1) ++ tenv3).
      change (A :: tenv1 ++ tenv2 ++ tenv3) with ((A :: tenv1) ++ tenv2 ++ tenv3).
      etransitivity. { apply (IHT3 (A :: tenv1) tenv2 tenv3 venv). }
      f_equal. apply ren_ty_ext.
      - intro m. unfold upren, scons, funcomp.
        destruct m; [reflexivity |].
        simpl. destruct (lt_dec m (length tenv1)), (lt_dec (S m) (S (length tenv1))); lia.
      - reflexivity. }
    unfold interp_forall.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2.
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros A HL HU.
    + rewrite <- (Hbinder A). apply Hbody; assumption.
    + rewrite (Hbinder A). apply Hbody; assumption.
  - (* TRefine *)
    assert (Hpred : forall x,
      eval_to_true (x :: venv) t <->
      eval_to_true (x :: venv)
        (ren_tm (fun n => if lt_dec n (length tenv1) then n else n + length tenv2) (upren id) t)).
    { intro x. rewrite ren_tm_upren_id. symmetry. apply eval_to_true_ren_ty. }
    unfold interp_refine.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT. rewrite <- (Hpred v). tauto.
  - (* TSigma *)
    assert (Hbinder : forall x,
      interp (tenv1 ++ tenv3) (x :: venv) T2 =
      interp (tenv1 ++ tenv2 ++ tenv3) (x :: venv)
        (ren_ty (fun n => if lt_dec n (length tenv1) then n else n + length tenv2) (upren id) T2)).
    { intro x. rewrite ren_ty_upren_id. apply IHT2. }
    unfold interp_sigma.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1.
    split; intros (v1 & v2 & Heq & Ha & Hb); exists v1, v2;
      (split; [exact Heq|]; split; [exact Ha|]).
    + rewrite <- (Hbinder v1). exact Hb.
    + rewrite (Hbinder v1). exact Hb.
  - (* TSum *)
    unfold interp_sum.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2. tauto.
  - (* TOr *)
    unfold interp_or.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2. tauto.
  - (* TAnd *)
    unfold interp_and.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHT1, <- IHT2. tauto.
  - (* TMuAll *)
    assert (Hbinder : forall A,
      interp (A :: tenv1 ++ tenv3) venv T =
      interp (A :: tenv1 ++ tenv2 ++ tenv3) venv
        (ren_ty (upren (fun n => if lt_dec n (length tenv1) then n else n + length tenv2)) id T)).
    { intro A.
      change (A :: tenv1 ++ tenv3) with ((A :: tenv1) ++ tenv3).
      change (A :: tenv1 ++ tenv2 ++ tenv3) with ((A :: tenv1) ++ tenv2 ++ tenv3).
      etransitivity. { apply (IHT (A :: tenv1) tenv2 tenv3 venv). }
      f_equal. apply ren_ty_ext.
      - intro m. unfold upren, scons, funcomp.
        destruct m; [reflexivity |].
        simpl. destruct (lt_dec m (length tenv1)), (lt_dec (S m) (S (length tenv1))); lia.
      - reflexivity. }
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    split; intros Hall n; specialize (Hall n);
      revert v Hall; apply interp_mu_eq_ext; intros X w;
      rewrite (Hbinder X); tauto.
Qed.

Lemma interp_env_ren_type: forall T tenv venv T',
  interp tenv venv T = interp (T'::tenv) venv (ren_ty S id T).
Proof.
  intros.
  change (T'::tenv) with ([] ++ [T'] ++ tenv).
  change tenv with ([] ++ tenv) at 1.
  rewrite (interp_weaken_type T [] [T'] tenv venv).
  f_equal. apply ren_ty_ext.
  - intro n. simpl. lia.
  - reflexivity.
Qed.
