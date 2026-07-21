(** * Substitution Lemmas

    Equational theory of the de Bruijn operations of [Subst]:
    extensionality, identity, and composition laws for renaming and
    substitution, and simplification lemmas for the [up] combinators. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.

(** ** Renaming extensionality *)

Lemma ren_ty_ext xi_ty xi_tm zeta_ty zeta_tm T :
  (forall n, xi_ty n = zeta_ty n) ->
  (forall n, xi_tm n = zeta_tm n) ->
  ren_ty xi_ty xi_tm T = ren_ty zeta_ty zeta_tm T
with ren_tm_ext xi_ty xi_tm zeta_ty zeta_tm t :
  (forall n, xi_ty n = zeta_ty n) ->
  (forall n, xi_tm n = zeta_tm n) ->
  ren_tm xi_ty xi_tm t = ren_tm zeta_ty zeta_tm t.
Proof.
  - destruct T; simpl; intros Hty Htm; f_equal; auto;
    (apply ren_ty_ext || apply ren_tm_ext); auto;
    intro m; destruct m; simpl; auto; unfold funcomp; auto.
  - destruct t; simpl; intros Hty Htm; f_equal; auto;
    (apply ren_ty_ext || apply ren_tm_ext); auto;
    intro m; try (destruct m; simpl; auto; unfold funcomp; auto);
    try (destruct m; simpl; auto; unfold funcomp; auto).
Qed.

(** ** Up extensionality helpers *)

Lemma up_ty_ty_ext sigma_ty tau_ty :
  (forall n, sigma_ty n = tau_ty n) ->
  forall n, up_ty_ty sigma_ty n = up_ty_ty tau_ty n.
Proof.
  intros H n. destruct n; [reflexivity|].
  unfold up_ty_ty, scons, funcomp. f_equal. auto using ren_ty_ext.
Qed.

Lemma up_ty_tm_ext sigma_tm tau_tm :
  (forall n, sigma_tm n = tau_tm n) ->
  forall n, up_ty_tm sigma_tm n = up_ty_tm tau_tm n.
Proof.
  intros H n. unfold up_ty_tm, funcomp. f_equal. auto.
Qed.

Lemma up_tm_ty_ext sigma_ty tau_ty :
  (forall n, sigma_ty n = tau_ty n) ->
  forall n, up_tm_ty sigma_ty n = up_tm_ty tau_ty n.
Proof.
  intros H n. unfold up_tm_ty, funcomp. f_equal. auto using ren_ty_ext.
Qed.

Lemma up_tm_tm_ext sigma_tm tau_tm :
  (forall n, sigma_tm n = tau_tm n) ->
  forall n, up_tm_tm sigma_tm n = up_tm_tm tau_tm n.
Proof.
  intros H n. destruct n; [reflexivity|].
  unfold up_tm_tm, scons, funcomp. f_equal. auto using ren_tm_ext.
Qed.

(** ** Substitution extensionality *)

Lemma subst_ty_ext sigma_ty tau_ty sigma_tm tau_tm T :
  (forall n, sigma_ty n = tau_ty n) ->
  (forall n, sigma_tm n = tau_tm n) ->
  subst_ty sigma_ty sigma_tm T = subst_ty tau_ty tau_tm T
with subst_tm_ext sigma_ty tau_ty sigma_tm tau_tm t :
  (forall n, sigma_ty n = tau_ty n) ->
  (forall n, sigma_tm n = tau_tm n) ->
  subst_tm sigma_ty sigma_tm t = subst_tm tau_ty tau_tm t.
Proof.
  - destruct T; simpl; intros Hty Htm; f_equal; auto;
    (apply subst_ty_ext || apply subst_tm_ext);
    auto using up_ty_ty_ext, up_ty_tm_ext, up_tm_ty_ext, up_tm_tm_ext.
  - destruct t; simpl; intros Hty Htm; f_equal; auto;
    (apply subst_ty_ext || apply subst_tm_ext);
    auto using up_ty_ty_ext, up_ty_tm_ext, up_tm_ty_ext, up_tm_tm_ext.
Qed.

(** ** Renaming identity *)

Lemma upren_id : forall n, upren id n = id n.
Proof. intros [|n]; reflexivity. Qed.

Lemma upren_upren_id : forall n, upren (upren id) n = id n.
Proof. intros [|[|n]]; reflexivity. Qed.

Lemma ren_ty_id T : ren_ty id id T = T
with ren_tm_id t : ren_tm id id t = t.
Proof.
  all: (destruct T || destruct t); simpl; f_equal; auto;
    try apply ren_ty_id; try apply ren_tm_id;
    try (etransitivity;
      [ (apply ren_ty_ext || apply ren_tm_ext);
        auto using upren_id, upren_upren_id
      | auto using ren_ty_id, ren_tm_id ]).
Qed.

(** Simplify [upren id] to [id] in renamings. *)
Lemma ren_ty_upren_id : forall xi T, ren_ty xi (upren id) T = ren_ty xi id T.
Proof. intros. apply ren_ty_ext; [reflexivity | exact upren_id]. Qed.

Lemma ren_tm_upren_id : forall xi t, ren_tm xi (upren id) t = ren_tm xi id t.
Proof. intros. apply ren_tm_ext; [reflexivity | exact upren_id]. Qed.

Lemma ren_ty_upren_upren_id : forall xi T, ren_ty xi (upren (upren id)) T = ren_ty xi id T.
Proof. intros. apply ren_ty_ext; [reflexivity | exact upren_upren_id]. Qed.

Lemma ren_tm_upren_upren_id : forall xi t, ren_tm xi (upren (upren id)) t = ren_tm xi id t.
Proof. intros. apply ren_tm_ext; [reflexivity | exact upren_upren_id]. Qed.

(** ** Substitution identity *)

Lemma up_ty_ty_id : forall n, up_ty_ty TVar n = TVar n.
Proof. intros [|n]; reflexivity. Qed.

Lemma up_ty_tm_id : forall n, up_ty_tm tvar n = tvar n.
Proof. intro n. unfold up_ty_tm, funcomp. simpl. reflexivity. Qed.

Lemma up_tm_ty_id : forall n, up_tm_ty TVar n = TVar n.
Proof. intro n. unfold up_tm_ty, funcomp. simpl. reflexivity. Qed.

Lemma up_tm_tm_id : forall n, up_tm_tm tvar n = tvar n.
Proof. intros [|n]; reflexivity. Qed.

Lemma up_tm_ty_up_tm_ty_id : forall n, up_tm_ty (up_tm_ty TVar) n = TVar n.
Proof. intro n. unfold up_tm_ty, funcomp. simpl. reflexivity. Qed.

Lemma up_tm_tm_up_tm_tm_id : forall n, up_tm_tm (up_tm_tm tvar) n = tvar n.
Proof. intros [|[|n]]; reflexivity. Qed.

Lemma subst_ty_id T : subst_ty TVar tvar T = T
with subst_tm_id t : subst_tm TVar tvar t = t.
Proof.
  all: (destruct T || destruct t); simpl; f_equal; auto;
    try apply subst_ty_id; try apply subst_tm_id;
    try (etransitivity;
      [ apply subst_ty_ext || apply subst_tm_ext;
        auto using up_ty_ty_id, up_ty_tm_id, up_tm_ty_id, up_tm_tm_id,
                   up_tm_ty_up_tm_ty_id, up_tm_tm_up_tm_tm_id
      | auto using subst_ty_id, subst_tm_id ]).
Qed.

(** Convenience: rewrite subst under term binders when sigma_ty = TVar *)
Lemma subst_ty_up_tm_ty_TVar : forall sigma_tm T,
  subst_ty (up_tm_ty TVar) sigma_tm T = subst_ty TVar sigma_tm T.
Proof. intros. apply subst_ty_ext. apply up_tm_ty_id. intro; reflexivity. Qed.

Lemma subst_tm_up_tm_ty_TVar : forall sigma_tm t,
  subst_tm (up_tm_ty TVar) sigma_tm t = subst_tm TVar sigma_tm t.
Proof. intros. apply subst_tm_ext. apply up_tm_ty_id. intro; reflexivity. Qed.

(** Convenience: subst_tm TVar (up_tm_tm tvar) t = t *)
Lemma subst_tm_up_tm_tm_tvar : forall t,
  subst_tm TVar (up_tm_tm tvar) t = t.
Proof.
  intros.
  etransitivity; [apply subst_tm_ext; [reflexivity | apply up_tm_tm_id] |].
  apply subst_tm_id.
Qed.

Lemma subst_tm_up_tm_tm_up_tm_tm_tvar : forall t,
  subst_tm TVar (up_tm_tm (up_tm_tm tvar)) t = t.
Proof.
  intros.
  etransitivity; [apply subst_tm_ext; [reflexivity | apply up_tm_tm_up_tm_tm_id] |].
  apply subst_tm_id.
Qed.

(** ** Renaming-substitution connection *)

Lemma up_ty_ty_ren xi_ty :
  forall n, up_ty_ty (xi_ty >> TVar) n = (upren xi_ty >> TVar) n.
Proof. intros [|n]; reflexivity. Qed.

Lemma up_ty_tm_ren xi_tm :
  forall n, up_ty_tm (xi_tm >> tvar) n = (xi_tm >> tvar) n.
Proof. intro n. reflexivity. Qed.

Lemma up_tm_ty_ren xi_ty :
  forall n, up_tm_ty (xi_ty >> TVar) n = (xi_ty >> TVar) n.
Proof. intro n. reflexivity. Qed.

Lemma up_tm_tm_ren xi_tm :
  forall n, up_tm_tm (xi_tm >> tvar) n = (upren xi_tm >> tvar) n.
Proof. intros [|n]; reflexivity. Qed.

Lemma up_tm_ty_up_tm_ty_ren xi_ty :
  forall n, up_tm_ty (up_tm_ty (xi_ty >> TVar)) n = (xi_ty >> TVar) n.
Proof. intro n. reflexivity. Qed.

Lemma up_tm_tm_up_tm_tm_ren xi_tm :
  forall n, up_tm_tm (up_tm_tm (xi_tm >> tvar)) n = (upren (upren xi_tm) >> tvar) n.
Proof. intros [|[|n]]; reflexivity. Qed.

Lemma ren_subst_ty xi_ty xi_tm T :
  ren_ty xi_ty xi_tm T = subst_ty (xi_ty >> TVar) (xi_tm >> tvar) T
with ren_subst_tm xi_ty xi_tm t :
  ren_tm xi_ty xi_tm t = subst_tm (xi_ty >> TVar) (xi_tm >> tvar) t.
Proof.
  all: (destruct T || destruct t); simpl; f_equal; auto;
    try apply ren_subst_ty; try apply ren_subst_tm;
    try (rewrite ren_subst_ty || rewrite ren_subst_tm);
    try (apply subst_ty_ext || apply subst_tm_ext);
    auto using up_ty_ty_ren, up_ty_tm_ren, up_tm_ty_ren, up_tm_tm_ren,
               up_tm_ty_up_tm_ty_ren, up_tm_tm_up_tm_tm_ren.
Qed.

(** ** Renaming composition *)

Lemma upren_comp xi zeta :
  forall n, upren (xi >> zeta) n = (upren xi >> upren zeta) n.
Proof. intros [|n]; reflexivity. Qed.

Lemma upren_upren_comp xi zeta :
  forall n, upren (upren (xi >> zeta)) n = (upren (upren xi) >> upren (upren zeta)) n.
Proof. intros [|[|n]]; reflexivity. Qed.

Lemma ren_comp_ty xi_ty xi_tm zeta_ty zeta_tm T :
  ren_ty zeta_ty zeta_tm (ren_ty xi_ty xi_tm T) = ren_ty (xi_ty >> zeta_ty) (xi_tm >> zeta_tm) T
with ren_comp_tm xi_ty xi_tm zeta_ty zeta_tm t :
  ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm t) = ren_tm (xi_ty >> zeta_ty) (xi_tm >> zeta_tm) t.
Proof.
  all: (destruct T || destruct t); simpl; f_equal; auto;
    try apply ren_comp_ty; try apply ren_comp_tm;
    try (rewrite ren_comp_ty || rewrite ren_comp_tm);
    try (apply ren_ty_ext || apply ren_tm_ext);
    auto using upren_comp, upren_upren_comp.
Qed.

(** ** Substitution after renaming *)

Lemma up_ty_ty_subst_ren xi_ty sigma_ty :
  forall n, up_ty_ty (xi_ty >> sigma_ty) n = (upren xi_ty >> up_ty_ty sigma_ty) n.
Proof.
  intros [|n]; [reflexivity|].
  unfold up_ty_ty, scons, funcomp, upren. simpl. reflexivity.
Qed.

Lemma up_ty_tm_subst_ren xi_tm sigma_tm :
  forall n, up_ty_tm (xi_tm >> sigma_tm) n = (xi_tm >> up_ty_tm sigma_tm) n.
Proof. intro n. reflexivity. Qed.

Lemma up_tm_ty_subst_ren xi_ty sigma_ty :
  forall n, up_tm_ty (xi_ty >> sigma_ty) n = (xi_ty >> up_tm_ty sigma_ty) n.
Proof. intro n. reflexivity. Qed.

Lemma up_tm_tm_subst_ren xi_tm sigma_tm :
  forall n, up_tm_tm (xi_tm >> sigma_tm) n = (upren xi_tm >> up_tm_tm sigma_tm) n.
Proof.
  intros [|n]; [reflexivity|].
  unfold up_tm_tm, scons, funcomp, upren. simpl. reflexivity.
Qed.

Lemma up_tm_ty_up_tm_ty_subst_ren xi_ty sigma_ty :
  forall n, up_tm_ty (up_tm_ty (xi_ty >> sigma_ty)) n =
            (xi_ty >> up_tm_ty (up_tm_ty sigma_ty)) n.
Proof. intro n. reflexivity. Qed.

Lemma up_tm_tm_up_tm_tm_subst_ren xi_tm sigma_tm :
  forall n, up_tm_tm (up_tm_tm (xi_tm >> sigma_tm)) n =
            (upren (upren xi_tm) >> up_tm_tm (up_tm_tm sigma_tm)) n.
Proof.
  intros [|[|n]]; [reflexivity|reflexivity|].
  unfold up_tm_tm, scons, funcomp, upren. simpl. reflexivity.
Qed.

Lemma subst_ren_ty xi_ty xi_tm sigma_ty sigma_tm T :
  subst_ty sigma_ty sigma_tm (ren_ty xi_ty xi_tm T) =
  subst_ty (xi_ty >> sigma_ty) (xi_tm >> sigma_tm) T
with subst_ren_tm xi_ty xi_tm sigma_ty sigma_tm t :
  subst_tm sigma_ty sigma_tm (ren_tm xi_ty xi_tm t) =
  subst_tm (xi_ty >> sigma_ty) (xi_tm >> sigma_tm) t.
Proof.
  all: (destruct T || destruct t); simpl; f_equal; auto;
    try apply subst_ren_ty; try apply subst_ren_tm;
    try (rewrite subst_ren_ty || rewrite subst_ren_tm);
    try (apply subst_ty_ext || apply subst_tm_ext);
    auto using up_ty_ty_subst_ren, up_ty_tm_subst_ren,
               up_tm_ty_subst_ren, up_tm_tm_subst_ren,
               up_tm_ty_up_tm_ty_subst_ren, up_tm_tm_up_tm_tm_subst_ren.
Qed.

(** ** Renaming after substitution *)

Lemma up_ty_ty_ren_subst xi_ty xi_tm sigma_ty :
  forall n, up_ty_ty (sigma_ty >> ren_ty xi_ty xi_tm) n =
            (up_ty_ty sigma_ty >> ren_ty (upren xi_ty) xi_tm) n.
Proof.
  intros [|n]; [reflexivity|].
  unfold up_ty_ty, scons, funcomp.
  rewrite !ren_comp_ty. apply ren_ty_ext; intro m; reflexivity.
Qed.

Lemma up_ty_tm_ren_subst xi_ty xi_tm sigma_tm :
  forall n, up_ty_tm (sigma_tm >> ren_tm xi_ty xi_tm) n =
            (up_ty_tm sigma_tm >> ren_tm (upren xi_ty) xi_tm) n.
Proof.
  intro n. unfold up_ty_tm, funcomp.
  rewrite !ren_comp_tm. apply ren_tm_ext; intro m; reflexivity.
Qed.

Lemma up_tm_ty_ren_subst xi_ty xi_tm sigma_ty :
  forall n, up_tm_ty (sigma_ty >> ren_ty xi_ty xi_tm) n =
            (up_tm_ty sigma_ty >> ren_ty xi_ty (upren xi_tm)) n.
Proof.
  intro n. unfold up_tm_ty, funcomp.
  rewrite !ren_comp_ty. apply ren_ty_ext; intro m; reflexivity.
Qed.

Lemma up_tm_tm_ren_subst xi_ty xi_tm sigma_tm :
  forall n, up_tm_tm (sigma_tm >> ren_tm xi_ty xi_tm) n =
            (up_tm_tm sigma_tm >> ren_tm xi_ty (upren xi_tm)) n.
Proof.
  intros [|n]; [reflexivity|].
  unfold up_tm_tm, scons, funcomp.
  rewrite !ren_comp_tm. apply ren_tm_ext; intro m; reflexivity.
Qed.

Lemma up_tm_ty_up_tm_ty_ren_subst xi_ty xi_tm sigma_ty :
  forall n, up_tm_ty (up_tm_ty (sigma_ty >> ren_ty xi_ty xi_tm)) n =
            (up_tm_ty (up_tm_ty sigma_ty) >> ren_ty xi_ty (upren (upren xi_tm))) n.
Proof.
  intro n. unfold up_tm_ty, funcomp.
  rewrite !ren_comp_ty. apply ren_ty_ext; intro m; reflexivity.
Qed.

Lemma up_tm_tm_up_tm_tm_ren_subst xi_ty xi_tm sigma_tm :
  forall n, up_tm_tm (up_tm_tm (sigma_tm >> ren_tm xi_ty xi_tm)) n =
            (up_tm_tm (up_tm_tm sigma_tm) >> ren_tm xi_ty (upren (upren xi_tm))) n.
Proof.
  intros [|[|n]]; [reflexivity|reflexivity|].
  unfold up_tm_tm, scons, funcomp.
  rewrite !ren_comp_tm. apply ren_tm_ext; intro m; reflexivity.
Qed.

Lemma ren_subst_comp_ty xi_ty xi_tm sigma_ty sigma_tm T :
  ren_ty xi_ty xi_tm (subst_ty sigma_ty sigma_tm T) =
  subst_ty (sigma_ty >> ren_ty xi_ty xi_tm) (sigma_tm >> ren_tm xi_ty xi_tm) T
with ren_subst_comp_tm xi_ty xi_tm sigma_ty sigma_tm t :
  ren_tm xi_ty xi_tm (subst_tm sigma_ty sigma_tm t) =
  subst_tm (sigma_ty >> ren_ty xi_ty xi_tm) (sigma_tm >> ren_tm xi_ty xi_tm) t.
Proof.
  all: (destruct T || destruct t); simpl; f_equal; auto;
    try apply ren_subst_comp_ty; try apply ren_subst_comp_tm;
    try (rewrite ren_subst_comp_ty || rewrite ren_subst_comp_tm);
    try (apply subst_ty_ext || apply subst_tm_ext);
    auto using up_ty_ty_ren_subst, up_ty_tm_ren_subst,
               up_tm_ty_ren_subst, up_tm_tm_ren_subst,
               up_tm_ty_up_tm_ty_ren_subst, up_tm_tm_up_tm_tm_ren_subst.
Qed.

(** ** Substitution composition *)

Lemma up_ty_ty_subst_comp tau_ty tau_tm sigma_ty :
  forall n, up_ty_ty (sigma_ty >> subst_ty tau_ty tau_tm) n =
            (up_ty_ty sigma_ty >> subst_ty (up_ty_ty tau_ty) (up_ty_tm tau_tm)) n.
Proof.
  intros [|n]; [reflexivity|].
  unfold up_ty_ty, scons, funcomp.
  rewrite ren_subst_comp_ty, subst_ren_ty. reflexivity.
Qed.

Lemma up_ty_tm_subst_comp tau_ty tau_tm sigma_tm :
  forall n, up_ty_tm (sigma_tm >> subst_tm tau_ty tau_tm) n =
            (up_ty_tm sigma_tm >> subst_tm (up_ty_ty tau_ty) (up_ty_tm tau_tm)) n.
Proof.
  intro n. unfold up_ty_tm, funcomp.
  rewrite ren_subst_comp_tm, subst_ren_tm. reflexivity.
Qed.

Lemma up_tm_ty_subst_comp tau_ty tau_tm sigma_ty :
  forall n, up_tm_ty (sigma_ty >> subst_ty tau_ty tau_tm) n =
            (up_tm_ty sigma_ty >> subst_ty (up_tm_ty tau_ty) (up_tm_tm tau_tm)) n.
Proof.
  intro n.
  change (ren_ty id S (subst_ty tau_ty tau_tm (sigma_ty n)) =
          subst_ty (up_tm_ty tau_ty) (up_tm_tm tau_tm) (ren_ty id S (sigma_ty n))).
  rewrite ren_subst_comp_ty, subst_ren_ty. reflexivity.
Qed.

Lemma up_tm_tm_subst_comp tau_ty tau_tm sigma_tm :
  forall n, up_tm_tm (sigma_tm >> subst_tm tau_ty tau_tm) n =
            (up_tm_tm sigma_tm >> subst_tm (up_tm_ty tau_ty) (up_tm_tm tau_tm)) n.
Proof.
  intros [|n]; [reflexivity|].
  change (ren_tm id S (subst_tm tau_ty tau_tm (sigma_tm n)) =
          subst_tm (up_tm_ty tau_ty) (up_tm_tm tau_tm) (ren_tm id S (sigma_tm n))).
  rewrite ren_subst_comp_tm, subst_ren_tm. reflexivity.
Qed.

Lemma up_tm_ty_up_tm_ty_subst_comp tau_ty tau_tm sigma_ty :
  forall n, up_tm_ty (up_tm_ty (sigma_ty >> subst_ty tau_ty tau_tm)) n =
            (up_tm_ty (up_tm_ty sigma_ty) >>
             subst_ty (up_tm_ty (up_tm_ty tau_ty)) (up_tm_tm (up_tm_tm tau_tm))) n.
Proof.
  intro n.
  change (ren_ty id S (ren_ty id S (subst_ty tau_ty tau_tm (sigma_ty n))) =
          subst_ty (up_tm_ty (up_tm_ty tau_ty)) (up_tm_tm (up_tm_tm tau_tm))
                   (ren_ty id S (ren_ty id S (sigma_ty n)))).
  rewrite ren_subst_comp_ty. rewrite ren_subst_comp_ty.
  rewrite subst_ren_ty. rewrite subst_ren_ty.
  apply subst_ty_ext; intro m; reflexivity.
Qed.

Lemma up_tm_tm_up_tm_tm_subst_comp tau_ty tau_tm sigma_tm :
  forall n, up_tm_tm (up_tm_tm (sigma_tm >> subst_tm tau_ty tau_tm)) n =
            (up_tm_tm (up_tm_tm sigma_tm) >>
             subst_tm (up_tm_ty (up_tm_ty tau_ty)) (up_tm_tm (up_tm_tm tau_tm))) n.
Proof.
  intros [|[|n]]; [reflexivity|reflexivity|].
  change (ren_tm id S (ren_tm id S (subst_tm tau_ty tau_tm (sigma_tm n))) =
          subst_tm (up_tm_ty (up_tm_ty tau_ty)) (up_tm_tm (up_tm_tm tau_tm))
                   (ren_tm id S (ren_tm id S (sigma_tm n)))).
  rewrite ren_subst_comp_tm. rewrite ren_subst_comp_tm.
  rewrite subst_ren_tm. rewrite subst_ren_tm.
  apply subst_tm_ext; intro m; reflexivity.
Qed.

Lemma subst_comp_ty sigma_ty sigma_tm tau_ty tau_tm T :
  subst_ty tau_ty tau_tm (subst_ty sigma_ty sigma_tm T) =
  subst_ty (sigma_ty >> subst_ty tau_ty tau_tm) (sigma_tm >> subst_tm tau_ty tau_tm) T
with subst_comp_tm sigma_ty sigma_tm tau_ty tau_tm t :
  subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm t) =
  subst_tm (sigma_ty >> subst_ty tau_ty tau_tm) (sigma_tm >> subst_tm tau_ty tau_tm) t.
Proof.
  all: (destruct T || destruct t); simpl; f_equal; auto;
    try apply subst_comp_ty; try apply subst_comp_tm;
    try (rewrite subst_comp_ty || rewrite subst_comp_tm);
    try (apply subst_ty_ext || apply subst_tm_ext);
    auto using up_ty_ty_subst_comp, up_ty_tm_subst_comp,
               up_tm_ty_subst_comp, up_tm_tm_subst_comp,
               up_tm_ty_up_tm_ty_subst_comp, up_tm_tm_up_tm_tm_subst_comp.
Qed.

(** ** Iterated up_tm_tm lemmas *)

Lemma upn_tm_ext : forall n f g,
  (forall x, f x = g x) ->
  forall x, upn_tm n f x = upn_tm n g x.
Proof.
  induction n; intros f g Hfg x; [apply Hfg|].
  simpl. apply up_tm_tm_ext. apply IHn. exact Hfg.
Qed.

Lemma upn_tm_ids : forall n x,
  upn_tm n tvar x = tvar x.
Proof.
  induction n; intros x; [reflexivity|].
  simpl.
  etransitivity.
  - apply up_tm_tm_ext. exact IHn.
  - apply up_tm_tm_id.
Qed.

Lemma iter_up_tm : forall (m x : nat) (f : var -> Term),
  upn_tm m f x = if lt_dec x m then tvar x
                  else ren_tm id (fun n => n + m) (f (x - m)).
Proof.
  induction m; intros x f.
  - simpl. destruct (lt_dec x 0); [lia|].
    rewrite Nat.sub_0_r. symmetry.
    etransitivity; [apply ren_tm_ext; [reflexivity | intro k; apply Nat.add_0_r] |].
    apply ren_tm_id.
  - simpl. unfold up_tm_tm, scons.
    destruct x.
    + destruct (lt_dec 0 (S m)); [reflexivity | lia].
    + unfold funcomp.
      rewrite IHm.
      destruct (lt_dec x m), (lt_dec (S x) (S m)); try lia.
      * simpl. reflexivity.
      * simpl.
        rewrite ren_comp_tm.
        apply ren_tm_ext; [reflexivity |].
        intro k. unfold funcomp. lia.
Qed.

(** ** Term-only shift substitution *)

(** Helper: term-only substitution with shift-by-k *)
Definition tm_shift (k : nat) : var -> Term := fun n => tvar (n + k).

(** Simplification: shift-by-0 substitution is identity *)
Lemma tm_shift_0_eq : forall m, tm_shift 0 m = tvar m.
Proof. intro m. unfold tm_shift. f_equal. apply Nat.add_0_r. Qed.

Lemma upn_tm_shift0_ids : forall n x,
  upn_tm n (tm_shift 0) x = tvar x.
Proof.
  intros n x.
  etransitivity; [apply upn_tm_ext; exact tm_shift_0_eq |].
  apply upn_tm_ids.
Qed.

Lemma subst_tm_upn_shift0 : forall n t,
  subst_tm TVar (upn_tm n (tm_shift 0)) t = t.
Proof.
  intros n t.
  etransitivity.
  - apply subst_tm_ext; [reflexivity | exact (upn_tm_shift0_ids n)].
  - apply subst_tm_id.
Qed.

Lemma up_tm_tm_shift0_id : forall x, up_tm_tm (tm_shift 0) x = tvar x.
Proof.
  intro x. etransitivity; [apply up_tm_tm_ext; exact tm_shift_0_eq |].
  apply up_tm_tm_id.
Qed.

Lemma subst_tm_shift0 : forall t,
  subst_tm TVar (tm_shift 0) t = t.
Proof.
  intro t.
  etransitivity; [apply subst_tm_ext; [reflexivity | exact tm_shift_0_eq] |].
  apply subst_tm_id.
Qed.

Lemma subst_tm_up_upn_shift0 : forall n t,
  subst_tm TVar (up_tm_tm (upn_tm n (tm_shift 0))) t = t.
Proof.
  intros n t.
  etransitivity.
  - apply subst_tm_ext; [reflexivity |].
    intro x. etransitivity; [apply up_tm_tm_ext; exact (upn_tm_shift0_ids n) |].
    apply up_tm_tm_id.
  - apply subst_tm_id.
Qed.

(** When sigma_ty = TVar, the "up" operations under binders simplify away.
    For term binders: up_tm_ty TVar = TVar (already above).
    For type binders: up_ty_ty TVar = TVar (already above).
    For type binders on term-only shift substitutions: *)
Lemma up_ty_tm_upn_tm_shift : forall m k n,
  up_ty_tm (upn_tm m (tm_shift k)) n = upn_tm m (tm_shift k) n.
Proof.
  intros m k n. unfold up_ty_tm, funcomp.
  rewrite iter_up_tm.
  destruct (lt_dec n m); simpl; reflexivity.
Qed.

(** Convenience: rewrite subst under type binders when sigma = upn_tm shift *)
Lemma subst_tm_up_ty_TVar_shift : forall m k t,
  subst_tm (up_ty_ty TVar) (up_ty_tm (upn_tm m (tm_shift k))) t =
  subst_tm TVar (upn_tm m (tm_shift k)) t.
Proof. intros. apply subst_tm_ext. apply up_ty_ty_id. apply up_ty_tm_upn_tm_shift. Qed.

Lemma subst_ty_up_ty_TVar_shift : forall m k T,
  subst_ty (up_ty_ty TVar) (up_ty_tm (upn_tm m (tm_shift k))) T =
  subst_ty TVar (upn_tm m (tm_shift k)) T.
Proof. intros. apply subst_ty_ext. apply up_ty_ty_id. apply up_ty_tm_upn_tm_shift. Qed.

(** Helper: up_ty_tm preserves upn_tm-based scons substitutions *)
Lemma up_ty_tm_upn_tm_scons_tvar : forall m i n,
  up_ty_tm (upn_tm m (tvar i .: tvar)) n = upn_tm m (tvar i .: tvar) n.
Proof.
  intros. unfold up_ty_tm, funcomp.
  rewrite iter_up_tm.
  destruct (lt_dec n m).
  - simpl. reflexivity.
  - destruct (n - m) as [|k]; simpl; reflexivity.
Qed.

(** abstract_term_var composed with its inverse is the identity. *)
Lemma abstract_term_var_cancel: forall i T,
  subst_ty TVar (tvar i .: tvar) (subst_ty TVar (abstract_term_var i) T) = T.
Proof.
  intros i T.
  rewrite subst_comp_ty.
  etransitivity; [| apply subst_ty_id].
  apply subst_ty_ext.
  - intro n. unfold funcomp. reflexivity.
  - intro j. unfold funcomp, abstract_term_var, scons.
    destruct (Nat.eq_dec j i) as [->|Hne]; simpl; reflexivity.
Qed.
