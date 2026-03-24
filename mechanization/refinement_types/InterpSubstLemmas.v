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
Require Import RefinementTypes.EvalSubstLemmas.
Require Import RefinementTypes.EvalTypeErasure.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.EvalShiftLemmas.
Require Import RefinementTypes.InterpShiftLemmas.

(** * Term variable substitution in interpretation *)

(** Helper: eval_to_true is preserved by environment substitution *)
Lemma eval_to_true_subst_env : forall p venv_prefix va venv i,
  nth_error venv i = Some va ->
  eval_to_true (venv_prefix ++ va :: venv) p <->
  eval_to_true (venv_prefix ++ venv)
    (subst_tm TVar (upn_tm (length venv_prefix) (tvar i .: tvar)) p).
Proof.
  intros p venv_prefix va venv i Hnth.
  unfold eval_to_true, term_has_semtype.
  split; intros H fuel r Heval.
  - (* forward: H about big env, Heval about small env *)
    destruct (eval_subst_env_bwd fuel p venv_prefix va venv i _ Hnth Heval) as [r' [Hrc Hr']].
    destruct r' as [[v'|]|]; [| | inversion Hrc].
    + inversion Hrc as [| | ? ? Hvc]; subst.
      destruct (H fuel (Some v') Hr') as [w [Hw Heq]].
      inversion Hw; subst. inversion Hvc; subst.
      exists (vbool true). auto.
    + inversion Hrc; subst.
      destruct (H fuel None Hr') as [w [Hw _]]. discriminate.
  - (* backward: H about small env, Heval about big env *)
    destruct (eval_subst_env_fwd fuel p venv_prefix va venv i _ Hnth Heval) as [r' [Hrc Hr']].
    destruct r' as [[v'|]|]; [| | inversion Hrc].
    + inversion Hrc as [| | ? ? Hvc]; subst.
      destruct (H fuel (Some v') Hr') as [w [Hw Heq]].
      inversion Hw; subst. inversion Hvc; subst.
      exists (vbool true). auto.
    + inversion Hrc; subst.
      destruct (H fuel None Hr') as [w [Hw _]]. discriminate.
Qed.

Lemma interp_subst_up_term: forall T tvars venv_prefix va venv i,
  nth_error venv i = Some va ->
  interp tvars (venv_prefix ++ va :: venv) T =
  interp tvars (venv_prefix ++ venv) (subst_ty TVar (upn_tm (length venv_prefix) (tvar i .: tvar)) T).
Proof.
  induction T as [j | | | | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 T3 IHT3 | T IHT t | T1 IHT1 T2 IHT2
    | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | | | T IHT];
    intros tvars venv_prefix va venv i Hnth; simpl; try reflexivity.
  - (* TFun *)
    assert (Hbinder : forall arg,
      interp tvars (arg :: venv_prefix ++ va :: venv) T2 =
      interp tvars (arg :: venv_prefix ++ venv)
        (subst_ty (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv_prefix) (tvar i .: tvar))) T2)).
    { intro arg. rewrite subst_ty_up_tm_ty_TVar.
      change (arg :: venv_prefix ++ va :: venv) with ((arg :: venv_prefix) ++ va :: venv).
      change (arg :: venv_prefix ++ venv) with ((arg :: venv_prefix) ++ venv).
      apply (IHT2 tvars (arg :: venv_prefix) va venv i Hnth). }
    unfold interp_fun.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- (IHT1 tvars venv_prefix va venv i Hnth).
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros arg Harg.
    + rewrite <- (Hbinder arg). apply Hbody. exact Harg.
    + rewrite (Hbinder arg). apply Hbody. exact Harg.
  - (* TForall *)
    assert (Hbinder : forall A,
      interp (A :: tvars) (venv_prefix ++ va :: venv) T3 =
      interp (A :: tvars) (venv_prefix ++ venv)
        (subst_ty (up_ty_ty TVar) (up_ty_tm (upn_tm (length venv_prefix) (tvar i .: tvar))) T3)).
    { intro A.
      rewrite (subst_ty_ext _ TVar _ _ T3 up_ty_ty_id
        (up_ty_tm_upn_tm_scons_tvar (length venv_prefix) i)).
      apply (IHT3 (A :: tvars) venv_prefix va venv i Hnth). }
    unfold interp_forall.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- (IHT1 tvars venv_prefix va venv i Hnth).
    rewrite <- (IHT2 tvars venv_prefix va venv i Hnth).
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros A HL HU.
    + rewrite <- (Hbinder A). apply Hbody; assumption.
    + rewrite (Hbinder A). apply Hbody; assumption.
  - (* TRefine *)
    assert (Hpred : forall x,
      eval_to_true (x :: venv_prefix ++ va :: venv) t <->
      eval_to_true (x :: venv_prefix ++ venv)
        (subst_tm (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv_prefix) (tvar i .: tvar))) t)).
    { intro x. rewrite subst_tm_up_tm_ty_TVar.
      replace (up_tm_tm (upn_tm (length venv_prefix) (tvar i .: tvar)))
        with (upn_tm (S (length venv_prefix)) (tvar i .: tvar))
        by reflexivity.
      change (S (length venv_prefix)) with (length (x :: venv_prefix)).
      change (x :: venv_prefix ++ va :: venv) with ((x :: venv_prefix) ++ va :: venv).
      change (x :: venv_prefix ++ venv) with ((x :: venv_prefix) ++ venv).
      apply (eval_to_true_subst_env t (x :: venv_prefix) va venv i Hnth). }
    unfold interp_refine.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- (IHT tvars venv_prefix va venv i Hnth).
    rewrite <- (Hpred v). tauto.
  - (* TSigma *)
    assert (Hbinder : forall x,
      interp tvars (x :: venv_prefix ++ va :: venv) T2 =
      interp tvars (x :: venv_prefix ++ venv)
        (subst_ty (up_tm_ty TVar) (up_tm_tm (upn_tm (length venv_prefix) (tvar i .: tvar))) T2)).
    { intro x. rewrite subst_ty_up_tm_ty_TVar.
      change (x :: venv_prefix ++ va :: venv) with ((x :: venv_prefix) ++ va :: venv).
      change (x :: venv_prefix ++ venv) with ((x :: venv_prefix) ++ venv).
      apply (IHT2 tvars (x :: venv_prefix) va venv i Hnth). }
    unfold interp_sigma.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- (IHT1 tvars venv_prefix va venv i Hnth).
    split; intros (v1 & v2 & Heq & Ha & Hb); exists v1, v2;
      (split; [exact Heq|]; split; [exact Ha|]).
    + rewrite <- (Hbinder v1). exact Hb.
    + rewrite (Hbinder v1). exact Hb.
  - (* TSum *)
    unfold interp_sum.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- (IHT1 tvars venv_prefix va venv i Hnth).
    rewrite <- (IHT2 tvars venv_prefix va venv i Hnth). tauto.
  - (* TOr *)
    unfold interp_or.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- (IHT1 tvars venv_prefix va venv i Hnth).
    rewrite <- (IHT2 tvars venv_prefix va venv i Hnth). tauto.
  - (* TAnd *)
    unfold interp_and.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- (IHT1 tvars venv_prefix va venv i Hnth).
    rewrite <- (IHT2 tvars venv_prefix va venv i Hnth). tauto.
  - (* TMuAll *)
    assert (Hbinder : forall X,
      interp (X :: tvars) (venv_prefix ++ va :: venv) T =
      interp (X :: tvars) (venv_prefix ++ venv)
        (subst_ty (up_ty_ty TVar) (up_ty_tm (upn_tm (length venv_prefix) (tvar i .: tvar))) T)).
    { intro X.
      rewrite (subst_ty_ext _ TVar _ _ T up_ty_ty_id
        (up_ty_tm_upn_tm_scons_tvar (length venv_prefix) i)).
      apply (IHT (X :: tvars) venv_prefix va venv i Hnth). }
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    split; intros Hall n; specialize (Hall n);
      revert v Hall; apply interp_mu_eq_ext; intros X w;
      rewrite (Hbinder X); tauto.
Qed.

Lemma interp_subst_term: forall T tvars venv i va,
  nth_error venv i = Some va ->
  interp tvars (va :: venv) T = interp tvars venv (subst_ty TVar (tvar i .: tvar) T).
Proof.
  intros.
  apply (interp_subst_up_term T tvars [] va venv i H).
Qed.

(** * Type variable substitution in interpretation *)

(** Helper: combined type + term weakening *)
Lemma interp_weaken_both: forall T tvars1 tvars2 venv_prefix venv,
  interp tvars2 venv T =
  interp (tvars1 ++ tvars2) (venv_prefix ++ venv)
    (ren_ty (plus (length tvars1)) (plus (length venv_prefix)) T).
Proof.
  intros T tvars1 tvars2 venv_prefix venv.
  (* Step 1: type weakening *)
  change tvars2 with ([] ++ tvars2) at 1.
  rewrite (interp_weaken_type T [] tvars1 tvars2 venv).
  (* Step 2: term weakening *)
  change venv with ([] ++ venv) at 1.
  rewrite (interp_weaken_term _ (tvars1 ++ tvars2) [] venv_prefix venv).
  f_equal.
  (* Show the compositions are equal *)
  rewrite subst_ren_ty, ren_subst_ty.
  apply subst_ty_ext.
  - intro m. unfold funcomp. simpl. destruct (lt_dec m 0); [lia|]. f_equal. lia.
  - intro m. simpl. unfold funcomp, tm_shift, id. f_equal. lia.
Qed.

(** ** The generalized type substitution function.

    [sigma_gen n A td] substitutes type variable [n] with [A] (shifted by [+n]
    for types and [+td] for terms), and decrements variables above [n].

    - [n]: the type variable being substituted (= [length tvars1])
    - [A]: the syntactic type to substitute
    - [td]: term depth (= [length venv_prefix])

    This substitution function properly propagates into term sub-expressions
    via [subst_ty ... tvar]. *)

Definition sigma_gen (n : nat) (A : Ty) (td : nat) : var -> Ty :=
  fun m => if Nat.eq_dec m n then ren_ty (plus n) (plus td) A
           else if Nat.ltb n m then TVar (m - 1)
           else TVar m.

(** [up_ty_ty] increments the substitution depth for type binders. *)
Lemma sigma_gen_up_ty_ty : forall n A td m,
  up_ty_ty (sigma_gen n A td) m = sigma_gen (S n) A td m.
Proof.
  intros n A td [|m].
  - (* m = 0 *)
    simpl. unfold sigma_gen. destruct (Nat.eq_dec 0 (S n)); [lia|].
    destruct (Nat.ltb (S n) 0) eqn:E; [apply Nat.ltb_lt in E; lia|].
    reflexivity.
  - (* m = S m *)
    unfold up_ty_ty, scons, funcomp, sigma_gen.
    destruct (Nat.eq_dec m n), (Nat.eq_dec (S m) (S n)); try lia; subst.
    + (* m = n *)
      rewrite ren_comp_ty. apply ren_ty_ext.
      * intro k. unfold funcomp. lia.
      * intro k. unfold funcomp. reflexivity.
    + (* m <> n *)
      destruct (Nat.ltb n m) eqn:Hlt1, (Nat.ltb (S n) (S m)) eqn:Hlt2;
        try (apply Nat.ltb_lt in Hlt1 || apply Nat.ltb_ge in Hlt1);
        try (apply Nat.ltb_lt in Hlt2 || apply Nat.ltb_ge in Hlt2);
        try lia.
      * simpl. f_equal. lia.
      * simpl. reflexivity.
Qed.

(** [up_tm_ty] increments the term depth. *)
Lemma sigma_gen_up_tm_ty : forall n A td m,
  up_tm_ty (sigma_gen n A td) m = sigma_gen n A (S td) m.
Proof.
  intros n A td m. unfold up_tm_ty, funcomp, sigma_gen.
  destruct (Nat.eq_dec m n); subst.
  - rewrite ren_comp_ty. apply ren_ty_ext.
    + intro k. unfold funcomp. reflexivity.
    + intro k. unfold funcomp. lia.
  - destruct (Nat.ltb n m); simpl; reflexivity.
Qed.

(** At depth 0, [sigma_gen 0 A 0] is [A .: TVar]. *)
Lemma sigma_gen_zero : forall A m,
  sigma_gen 0 A 0 m = (A .: TVar) m.
Proof.
  intros A [|m]; unfold sigma_gen; simpl.
  - rewrite ren_ty_id. reflexivity.
  - f_equal. lia.
Qed.

(** Generalized type substitution lemma.
    Substitutes type variable [length tvars1] in the extended type env
    [tvars1 ++ SA :: tvars2] with syntactic type A. *)
Lemma interp_subst_gen: forall B A tvars1 tvars2 venv_prefix venv,
  interp (tvars1 ++ interp tvars2 venv A :: tvars2) (venv_prefix ++ venv) B =
  interp (tvars1 ++ tvars2) (venv_prefix ++ venv)
    (subst_ty (sigma_gen (length tvars1) A (length venv_prefix)) tvar B).
Proof.
  induction B as [m | | | | B1 IHB1 B2 IHB2 | B1 IHB1 B2 IHB2 B3 IHB3 | B IHB t | B1 IHB1 B2 IHB2
    | B1 IHB1 B2 IHB2 | B1 IHB1 B2 IHB2 | B1 IHB1 B2 IHB2 | | | B IHB];
    intros A tvars1 tvars2 venv_prefix venv; simpl; try reflexivity.
  - (* TVar m *)
    unfold sigma_gen, interp_var.
    destruct (Nat.eq_dec m (length tvars1)) as [Heq | Hneq].
    + (* m = length tvars1: the substituted variable *)
      subst m. rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag. simpl.
      change (fun v : Value => interp tvars2 venv A v) with (interp tvars2 venv A).
      apply interp_weaken_both.
    + destruct (Nat.ltb (length tvars1) m) eqn:Hltb.
      * (* m > length tvars1 *)
        apply Nat.ltb_lt in Hltb. simpl. unfold interp_var.
        rewrite (nth_error_app2 tvars1 (interp tvars2 venv A :: tvars2)) by lia.
        rewrite (nth_error_app2 tvars1 tvars2) by lia.
        replace (m - length tvars1) with (S (m - length tvars1 - 1)) by lia.
        simpl.
        replace (m - 1 - length tvars1) with (m - length tvars1 - 1) by lia.
        reflexivity.
      * (* m < length tvars1 *)
        apply Nat.ltb_ge in Hltb. simpl. unfold interp_var.
        assert (m < length tvars1) by lia.
        rewrite nth_error_app1 by lia.
        rewrite nth_error_app1 by lia. reflexivity.
  - (* TFun *)
    assert (Hbinder : forall arg,
      interp (tvars1 ++ interp tvars2 venv A :: tvars2) (arg :: venv_prefix ++ venv) B2 =
      interp (tvars1 ++ tvars2) (arg :: venv_prefix ++ venv)
        (subst_ty (up_tm_ty (sigma_gen (length tvars1) A (length venv_prefix)))
                  (up_tm_tm tvar) B2)).
    { intro arg.
      rewrite (subst_ty_ext _ _ _ _ B2 (sigma_gen_up_tm_ty _ _ _) up_tm_tm_id).
      change (arg :: venv_prefix ++ venv) with ((arg :: venv_prefix) ++ venv).
      apply (IHB2 A tvars1 tvars2 (arg :: venv_prefix) venv). }
    unfold interp_fun.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHB1.
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros arg Harg.
    + rewrite <- (Hbinder arg). apply Hbody. exact Harg.
    + rewrite (Hbinder arg). apply Hbody. exact Harg.
  - (* TForall *)
    assert (Hbinder : forall A',
      interp (A' :: tvars1 ++ interp tvars2 venv A :: tvars2) (venv_prefix ++ venv) B3 =
      interp (A' :: tvars1 ++ tvars2) (venv_prefix ++ venv)
        (subst_ty (up_ty_ty (sigma_gen (length tvars1) A (length venv_prefix)))
                  (up_ty_tm tvar) B3)).
    { intro A'.
      rewrite (subst_ty_ext _ _ _ _ B3 (sigma_gen_up_ty_ty _ _ _) up_ty_tm_id).
      change (A' :: tvars1 ++ interp tvars2 venv A :: tvars2)
        with ((A' :: tvars1) ++ interp tvars2 venv A :: tvars2).
      change (A' :: tvars1 ++ tvars2) with ((A' :: tvars1) ++ tvars2).
      apply (IHB3 A (A' :: tvars1) tvars2 venv_prefix venv). }
    unfold interp_forall.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHB1, <- IHB2.
    split; intros (env' & body & Heq & Hbody); exists env', body;
      (split; [exact Heq|]); intros A' HL HU.
    + rewrite <- (Hbinder A'). apply Hbody; assumption.
    + rewrite (Hbinder A'). apply Hbody; assumption.
  - (* TRefine *)
    assert (Hpred : forall x,
      eval_to_true (x :: venv_prefix ++ venv) t <->
      eval_to_true (x :: venv_prefix ++ venv)
        (subst_tm (up_tm_ty (sigma_gen (length tvars1) A (length venv_prefix)))
                  (up_tm_tm tvar) t)).
    { intro x. symmetry. apply eval_to_true_subst_ty_gen. apply up_tm_tm_id. }
    unfold interp_refine.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHB. rewrite <- (Hpred v). tauto.
  - (* TSigma *)
    assert (Hbinder : forall x,
      interp (tvars1 ++ interp tvars2 venv A :: tvars2) (x :: venv_prefix ++ venv) B2 =
      interp (tvars1 ++ tvars2) (x :: venv_prefix ++ venv)
        (subst_ty (up_tm_ty (sigma_gen (length tvars1) A (length venv_prefix)))
                  (up_tm_tm tvar) B2)).
    { intro x.
      rewrite (subst_ty_ext _ _ _ _ B2 (sigma_gen_up_tm_ty _ _ _) up_tm_tm_id).
      change (x :: venv_prefix ++ venv) with ((x :: venv_prefix) ++ venv).
      apply (IHB2 A tvars1 tvars2 (x :: venv_prefix) venv). }
    unfold interp_sigma.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHB1.
    split; intros (v1 & v2 & Heq & Ha & Hb); exists v1, v2;
      (split; [exact Heq|]; split; [exact Ha|]).
    + rewrite <- (Hbinder v1). exact Hb.
    + rewrite (Hbinder v1). exact Hb.
  - (* TSum *)
    unfold interp_sum.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHB1, <- IHB2. tauto.
  - (* TOr *)
    unfold interp_or.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHB1, <- IHB2. tauto.
  - (* TAnd *)
    unfold interp_and.
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    rewrite <- IHB1, <- IHB2. tauto.
  - (* TMuAll *)
    assert (Hbinder : forall A',
      interp (A' :: tvars1 ++ interp tvars2 venv A :: tvars2) (venv_prefix ++ venv) B =
      interp (A' :: tvars1 ++ tvars2) (venv_prefix ++ venv)
        (subst_ty (up_ty_ty (sigma_gen (length tvars1) A (length venv_prefix)))
                  (up_ty_tm tvar) B)).
    { intro A'.
      rewrite (subst_ty_ext _ _ _ _ B (sigma_gen_up_ty_ty _ _ _) up_ty_tm_id).
      change (A' :: tvars1 ++ interp tvars2 venv A :: tvars2)
        with ((A' :: tvars1) ++ interp tvars2 venv A :: tvars2).
      change (A' :: tvars1 ++ tvars2) with ((A' :: tvars1) ++ tvars2).
      apply (IHB A (A' :: tvars1) tvars2 venv_prefix venv). }
    apply functional_extensionality; intro v.
    apply propositional_extensionality.
    split; intros Hall n; specialize (Hall n);
      revert v Hall; apply interp_mu_eq_ext; intros X w;
      rewrite (Hbinder X); tauto.
Qed.

Lemma interp_subst: forall B A tvars venv,
  interp (interp tvars venv A :: tvars) venv B =
  interp tvars venv (ty_subst B A).
Proof.
  intros B A tvars venv.
  change (interp tvars venv A :: tvars) with ([] ++ interp tvars venv A :: tvars).
  change venv with ([] ++ venv) at 2.
  rewrite (interp_subst_gen B A [] tvars [] venv).
  simpl. unfold ty_subst. f_equal. apply subst_ty_ext.
  - apply sigma_gen_zero.
  - reflexivity.
Qed.
