From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.

(** * Type Erasure

    Evaluation is insensitive to type annotations (types are erased at run
    time, §3.2). We formalize this by defining erasure functions that
    replace all type annotations with [TUnit], and proving that evaluation
    commutes with erasure. *)

Fixpoint erase_ty_in_tm (t : Term) : Term :=
  match t with
  | tunit => tunit
  | tbool b => tbool b
  | tint32 z => tint32 z
  | tvar n => tvar n
  | tabs _ b => tabs TUnit (erase_ty_in_tm b)
  | tapp f a => tapp (erase_ty_in_tm f) (erase_ty_in_tm a)
  | ttabs _ _ b => ttabs TUnit TUnit (erase_ty_in_tm b)
  | ttapp e _ => ttapp (erase_ty_in_tm e) TUnit
  | tlet _ a b => tlet TUnit (erase_ty_in_tm a) (erase_ty_in_tm b)
  | tpair a b => tpair (erase_ty_in_tm a) (erase_ty_in_tm b)
  | tmatch_pair e b => tmatch_pair (erase_ty_in_tm e) (erase_ty_in_tm b)
  | tinl _ e => tinl TUnit (erase_ty_in_tm e)
  | tinr _ e => tinr TUnit (erase_ty_in_tm e)
  | tmatch_sum e l r => tmatch_sum (erase_ty_in_tm e) (erase_ty_in_tm l) (erase_ty_in_tm r)
  | tbin_op op a b => tbin_op op (erase_ty_in_tm a) (erase_ty_in_tm b)
  | tif c t f => tif (erase_ty_in_tm c) (erase_ty_in_tm t) (erase_ty_in_tm f)
  | tdiverge => tdiverge
  | tloop a body => tloop (erase_ty_in_tm a) (erase_ty_in_tm body)
  end.

Fixpoint erase_ty_in_val (v : Value) : Value :=
  match v with
  | vunit => vunit
  | vbool b => vbool b
  | vint32 z => vint32 z
  | vpair v1 v2 => vpair (erase_ty_in_val v1) (erase_ty_in_val v2)
  | vinl v => vinl (erase_ty_in_val v)
  | vinr v => vinr (erase_ty_in_val v)
  | vabs env b => vabs (map erase_ty_in_val env) (erase_ty_in_tm b)
  | vtabs env b => vtabs (map erase_ty_in_val env) (erase_ty_in_tm b)
  end.

(** Type renaming in a term does not affect its erasure. *)
Lemma erase_ty_in_tm_ren : forall t xi,
  erase_ty_in_tm (ren_tm xi id t) = erase_ty_in_tm t.
Proof.
  induction t; intros xi; simpl; f_equal; auto;
    try (rewrite ren_tm_upren_id; auto);
    try (rewrite ren_tm_upren_upren_id; auto).
Qed.

(** Helper: nth_error commutes with map. *)
Lemma nth_error_map {A B : Type} (f : A -> B) (l : list A) (n : nat) :
  nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  revert n. induction l; intros [|n]; simpl; auto.
Qed.

(** Helper for matching on option (option Value) results. *)
Definition oov_map (f : Value -> Value) (r : option (option Value)) : option (option Value) :=
  match r with
  | None => None
  | Some None => Some None
  | Some (Some v) => Some (Some (f v))
  end.

Lemma map_erase_cons : forall v env,
  erase_ty_in_val v :: map erase_ty_in_val env = map erase_ty_in_val (v :: env).
Proof. reflexivity. Qed.

Lemma run_loop_erase_ty : forall step1 step2 n va,
  (forall v, oov_map erase_ty_in_val (step1 v) = step2 (erase_ty_in_val v)) ->
  oov_map erase_ty_in_val (run_loop step1 n va) =
  run_loop step2 n (erase_ty_in_val va).
Proof.
  intros step1 step2 n.
  induction n; intros va Hstep; simpl; try reflexivity.
  rewrite <- Hstep.
  destruct (step1 va) as [[[|b0|z0|v1' v2'|vinlv|vinrv|envf body|envf body]|]|];
    simpl; try reflexivity.
  all: try (apply IHn; exact Hstep).
Qed.

(** Main simulation: evaluation commutes with type erasure. *)
Lemma eval_erase_ty : forall fuel env t,
  oov_map erase_ty_in_val (eval fuel env t) =
  eval fuel (map erase_ty_in_val env) (erase_ty_in_tm t).
Proof.
  induction fuel as [|fuel IH]; intros env t.
  { simpl. reflexivity. }
  destruct t; simpl; try reflexivity.
  - (* tvar *)
    rewrite nth_error_map.
    destruct (nth_error env v); simpl; reflexivity.
  - (* tapp *)
    rewrite <- (IH env t1).
    destruct (eval fuel env t1) as [[[|b0|z0|v1' v2'|vinlv|vinrv|envf body|envf body]|]|];
      simpl; try reflexivity.
    (* vabs case *)
    rewrite <- (IH env t2).
    destruct (eval fuel env t2) as [[va|]|]; simpl; try reflexivity.
    rewrite map_erase_cons. apply IH.
  - (* ttapp *)
    rewrite <- (IH env t).
    destruct (eval fuel env t) as [[[|b0|z0|v1' v2'|vinlv|vinrv|envf body|envf body]|]|];
      simpl; try reflexivity.
    apply IH.
  - (* tlet *)
    rewrite <- (IH env t2).
    destruct (eval fuel env t2) as [[ve|]|]; simpl; try reflexivity.
    rewrite map_erase_cons. apply IH.
  - (* tpair *)
    rewrite <- (IH env t1).
    destruct (eval fuel env t1) as [[v1|]|]; simpl; try reflexivity.
    rewrite <- (IH env t2).
    destruct (eval fuel env t2) as [[v2|]|]; simpl; try reflexivity.
  - (* tmatch_pair *)
    rewrite <- (IH env t1).
    destruct (eval fuel env t1) as [[[|b0|z0|v1' v2'|vinlv|vinrv|envf body|envf body]|]|];
      simpl; try reflexivity.
    change (erase_ty_in_val v2' :: erase_ty_in_val v1' :: map erase_ty_in_val env)
      with (map erase_ty_in_val (v2' :: v1' :: env)).
    apply IH.
  - (* tinl *)
    rewrite <- (IH env t0).
    destruct (eval fuel env t0) as [[ve|]|]; simpl; try reflexivity.
  - (* tinr *)
    rewrite <- (IH env t0).
    destruct (eval fuel env t0) as [[ve|]|]; simpl; try reflexivity.
  - (* tmatch_sum *)
    rewrite <- (IH env t1).
    destruct (eval fuel env t1) as [[[|b0|z0|v1' v2'|vinlv|vinrv|envf body|envf body]|]|];
      simpl; try reflexivity.
    + change (erase_ty_in_val vinlv :: map erase_ty_in_val env)
        with (map erase_ty_in_val (vinlv :: env)).
      apply IH.
    + change (erase_ty_in_val vinrv :: map erase_ty_in_val env)
        with (map erase_ty_in_val (vinrv :: env)).
      apply IH.
  - (* tbin_op *)
    rewrite <- (IH env t1).
    destruct (eval fuel env t1) as [[va|]|]; simpl; try reflexivity.
    rewrite <- (IH env t2).
    destruct (eval fuel env t2) as [[vb|]|]; simpl; try reflexivity.
    destruct va; destruct vb; simpl; try reflexivity;
      destruct b; simpl; reflexivity.
  - (* tif *)
    rewrite <- (IH env t1).
    destruct (eval fuel env t1) as [[[|b1|z0|v1' v2'|vinlv|vinrv|envf body|envf body]|]|];
      simpl; try reflexivity.
    destruct b1; apply IH.
  - (* tloop *)
    rewrite <- (IH env t1).
    destruct (eval fuel env t1) as [[va|]|]; simpl; try reflexivity.
    apply run_loop_erase_ty.
    intros v. rewrite map_erase_cons. apply IH.
Qed.

Lemma erase_ty_in_val_vbool_true : forall v,
  erase_ty_in_val v = vbool true -> v = vbool true.
Proof. destruct v; simpl; intros H; try discriminate. injection H as ->. reflexivity. Qed.

(** If sigma_tm is extensionally tvar, lifting preserves this property. *)
Lemma up_tm_tm_tvar_ext sigma_tm :
  (forall n, sigma_tm n = tvar n) -> forall n, up_tm_tm sigma_tm n = tvar n.
Proof.
  intros H n. etransitivity. apply up_tm_tm_ext. exact H. apply up_tm_tm_id.
Qed.

Lemma up_ty_tm_tvar_ext sigma_tm :
  (forall n, sigma_tm n = tvar n) -> forall n, up_ty_tm sigma_tm n = tvar n.
Proof.
  intros H n. etransitivity. apply up_ty_tm_ext. exact H. apply up_ty_tm_id.
Qed.

Lemma up_tm_tm_up_tm_tm_tvar_ext sigma_tm :
  (forall n, sigma_tm n = tvar n) -> forall n, up_tm_tm (up_tm_tm sigma_tm) n = tvar n.
Proof.
  intros H. apply up_tm_tm_tvar_ext. apply up_tm_tm_tvar_ext. exact H.
Qed.

(** Type substitution in a term does not affect its erasure. *)
Lemma erase_ty_in_tm_subst_gen : forall t sigma_ty sigma_tm,
  (forall n, sigma_tm n = tvar n) ->
  erase_ty_in_tm (subst_tm sigma_ty sigma_tm t) = erase_ty_in_tm t.
Proof.
  induction t; intros sigma_ty sigma_tm Htm; simpl;
    try rewrite (Htm v); (* tvar case *)
    try reflexivity;
    f_equal;
    eauto using up_tm_tm_tvar_ext, up_ty_tm_tvar_ext, up_tm_tm_up_tm_tm_tvar_ext.
Qed.

Corollary erase_ty_in_tm_subst : forall t sigma_ty,
  erase_ty_in_tm (subst_tm sigma_ty tvar t) = erase_ty_in_tm t.
Proof.
  intros. apply erase_ty_in_tm_subst_gen. reflexivity.
Qed.
