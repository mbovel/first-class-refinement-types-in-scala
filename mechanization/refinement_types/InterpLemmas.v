(** * Interpretation Lemmas (Lemmas 3.3 to 3.6)

    The value interpretation is invariant under renaming and substitution
    of both kinds of variables, provided the environments are adjusted
    accordingly:
    - [interp_ren]: a simultaneous type and term renaming, with the type
      variable and value environments related pointwise through the
      renamings ([env_ren]). Term weakening (Lemma 3.3), term substitution
      (Lemma 3.4) and type weakening (Lemma 3.5) are instances.
    - [interp_subst_ty]: a type substitution together with a term
      renaming, where each type variable of the source environment denotes
      the interpretation of the type substituted for it. Type substitution
      (Lemma 3.6) is an instance.

    The lemmas are stated in de Bruijn form: extending an environment
    corresponds to an explicit index shift on the type, and the freshness
    side conditions of the paper are implicit. *)

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
Require Import RefinementTypes.EvalLemmas.
Require Import RefinementTypes.Interp.

(** ** Renaming *)

Lemma interp_ren : forall T tvars1 venv1 tvars2 venv2 zeta xi,
  env_ren tvars1 zeta tvars2 ->
  env_ren venv1 xi venv2 ->
  interp tvars1 venv1 T = interp tvars2 venv2 (ren_ty zeta xi T).
Proof.
  induction T as [i | | | | A IHA B IHB | L IHL U IHU B IHB | A IHA p | A IHA B IHB
    | A IHA B IHB | A IHA B IHB | A IHA B IHB | | | B IHB];
    intros tvars1 venv1 tvars2 venv2 zeta xi Htv Hve; simpl; try reflexivity.
  - (* TVar *) unfold interp_var. rewrite (Htv i). reflexivity.
  - (* TFun *)
    f_equal; [apply IHA; assumption |].
    apply functional_extensionality; intro arg.
    apply IHB; [assumption | apply env_ren_cons; assumption].
  - (* TForall *)
    f_equal; [apply IHL; assumption | apply IHU; assumption |].
    apply functional_extensionality; intro X.
    apply IHB; [apply env_ren_cons; assumption | assumption].
  - (* TRefine *)
    rewrite (IHA _ _ _ _ _ _ Htv Hve). unfold interp_refine.
    apply functional_extensionality; intro v. f_equal.
    apply propositional_extensionality.
    apply eval_to_true_ren. apply env_ren_cons. assumption.
  - (* TSigma *)
    f_equal; [apply IHA; assumption |].
    apply functional_extensionality; intro v1.
    apply IHB; [assumption | apply env_ren_cons; assumption].
  - (* TSum *) f_equal; [apply IHA | apply IHB]; assumption.
  - (* TOr *) f_equal; [apply IHA | apply IHB]; assumption.
  - (* TAnd *) f_equal; [apply IHA | apply IHB]; assumption.
  - (* TMuAll *)
    assert (Heq : (fun X : SemTy => interp (X :: tvars1) venv1 B) =
                  (fun X : SemTy => interp (X :: tvars2) venv2 (ren_ty (upren zeta) xi B))).
    { apply functional_extensionality; intro X.
      apply IHB; [apply env_ren_cons; assumption | assumption]. }
    rewrite Heq. reflexivity.
Qed.

(** ** Type substitution *)

(** The hypothesis of [interp_subst_ty], that each type variable denotes
    the interpretation of the type substituted for it, is preserved when
    going under a term binder ... *)
Lemma interp_var_up_tm_ty : forall tvars1 tvars2 venv2 sigma v,
  (forall i, interp_var tvars1 i = interp tvars2 venv2 (sigma i)) ->
  forall i, interp_var tvars1 i = interp tvars2 (v :: venv2) (up_tm_ty sigma i).
Proof.
  intros tvars1 tvars2 venv2 sigma v H i. rewrite H.
  apply (interp_ren (sigma i) tvars2 venv2 tvars2 (v :: venv2) id S);
    intro x; reflexivity.
Qed.

(** ... and under a type binder. *)
Lemma interp_var_up_ty_ty : forall tvars1 tvars2 venv2 sigma X,
  (forall i, interp_var tvars1 i = interp tvars2 venv2 (sigma i)) ->
  forall i, interp_var (X :: tvars1) i = interp (X :: tvars2) venv2 (up_ty_ty sigma i).
Proof.
  intros tvars1 tvars2 venv2 sigma X H [|i]; [reflexivity |].
  change (interp_var (X :: tvars1) (S i)) with (interp_var tvars1 i). rewrite H.
  apply (interp_ren (sigma i) tvars2 venv2 (X :: tvars2) venv2 S id);
    intro x; reflexivity.
Qed.

Lemma interp_subst_ty : forall T tvars1 venv1 tvars2 venv2 sigma xi,
  (forall i, interp_var tvars1 i = interp tvars2 venv2 (sigma i)) ->
  env_ren venv1 xi venv2 ->
  interp tvars1 venv1 T = interp tvars2 venv2 (subst_ty sigma (xi >> tvar) T).
Proof.
  induction T as [i | | | | A IHA B IHB | L IHL U IHU B IHB | A IHA p | A IHA B IHB
    | A IHA B IHB | A IHA B IHB | A IHA B IHB | | | B IHB];
    intros tvars1 venv1 tvars2 venv2 sigma xi Hty Hve; simpl; try reflexivity.
  - (* TVar *) apply Hty.
  - (* TFun *)
    rewrite subst_ty_up_tm_ren.
    f_equal; [apply IHA; assumption |].
    apply functional_extensionality; intro arg.
    apply IHB; [apply interp_var_up_tm_ty; assumption | apply env_ren_cons; assumption].
  - (* TForall *)
    rewrite subst_ty_up_ty_ren.
    f_equal; [apply IHL; assumption | apply IHU; assumption |].
    apply functional_extensionality; intro X.
    apply IHB; [apply interp_var_up_ty_ty; assumption | assumption].
  - (* TRefine *)
    rewrite (IHA _ _ _ _ _ _ Hty Hve), subst_tm_up_tm_ren. unfold interp_refine.
    apply functional_extensionality; intro v. f_equal.
    apply propositional_extensionality.
    apply eval_to_true_subst_ren. apply env_ren_cons. assumption.
  - (* TSigma *)
    rewrite subst_ty_up_tm_ren.
    f_equal; [apply IHA; assumption |].
    apply functional_extensionality; intro v1.
    apply IHB; [apply interp_var_up_tm_ty; assumption | apply env_ren_cons; assumption].
  - (* TSum *) f_equal; [apply IHA | apply IHB]; assumption.
  - (* TOr *) f_equal; [apply IHA | apply IHB]; assumption.
  - (* TAnd *) f_equal; [apply IHA | apply IHB]; assumption.
  - (* TMuAll *)
    rewrite subst_ty_up_ty_ren.
    assert (Heq : (fun X : SemTy => interp (X :: tvars1) venv1 B) =
                  (fun X : SemTy => interp (X :: tvars2) venv2
                     (subst_ty (up_ty_ty sigma) (xi >> tvar) B))).
    { apply functional_extensionality; intro X.
      apply IHB; [apply interp_var_up_ty_ty; assumption | assumption]. }
    rewrite Heq. reflexivity.
Qed.

(** ** Term weakening (Lemma 3.3) *)

Lemma interp_env_ren_term: forall T tenv venv v,
  interp tenv venv T = interp tenv (v::venv) (ren_ty id S T).
Proof. intros. apply interp_ren; intro x; reflexivity. Qed.

(** ** Term substitution (Lemma 3.4) *)

Lemma interp_subst_term: forall T tvars venv i va,
  nth_error venv i = Some va ->
  interp tvars (va :: venv) T = interp tvars venv (subst_ty TVar (tvar i .: tvar) T).
Proof.
  intros T tvars venv i va Hnth.
  change (tvar i .: tvar) with (upn_tm 0 (tvar i .: tvar)).
  rewrite subst_ty_subst_ren.
  apply interp_ren; [intro x; reflexivity | exact (env_ren_subst [] va venv i Hnth)].
Qed.

(** ** Type weakening (Lemma 3.5) *)

Lemma interp_weaken_type: forall T tenv1 tenv2 tenv3 venv,
  interp (tenv1 ++ tenv3) venv T =
  interp (tenv1 ++ tenv2 ++ tenv3) venv
    (ren_ty (fun n => if lt_dec n (length tenv1) then n else n + length tenv2) id T).
Proof.
  intros. apply interp_ren; [exact (env_ren_shift tenv1 tenv2 tenv3) | intro x; reflexivity].
Qed.

Lemma interp_env_ren_type: forall T tenv venv T',
  interp tenv venv T = interp (T'::tenv) venv (ren_ty S id T).
Proof. intros. apply interp_ren; intro x; reflexivity. Qed.

(** ** Type substitution (Lemma 3.6) *)

Lemma interp_subst: forall B A tvars venv,
  interp (interp tvars venv A :: tvars) venv B = interp tvars venv (ty_subst B A).
Proof.
  intros B A tvars venv. unfold ty_subst.
  rewrite <- (subst_ty_ext (A .: TVar) (A .: TVar) (id >> tvar) tvar B
                (fun _ => eq_refl) (fun _ => eq_refl)).
  apply interp_subst_ty; [intros [|i]; reflexivity | intro x; reflexivity].
Qed.
