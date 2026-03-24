
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.EvalLemmas.

(** ** Semantic type definition *)

Definition SemTy := Value -> Prop.

(** ** Term has semantic type

    A term has a semantic type if it can evaluate (given enough fuel) to a value
    that satisfies the semantic type. *)

Definition term_has_semtype (env: list Value) (t: Term) (ty: SemTy) : Prop :=
  forall fuel r, eval fuel env t = Some r ->
    exists v, r = Some v /\ ty v.

(** ** Type interpretation components *)

(** Type variable interpretation: looks up in the semantic type environment *)
Definition interp_var (tenv: list SemTy) (i: nat) (v: Value) : Prop :=
  match (nth_error tenv i) with
  | Some A => A v
  | None => False
  end.

Definition interp_unit (v: Value) : Prop :=
  v = vunit.

Definition interp_bool (v: Value) : Prop :=
  exists b, v = vbool b.

Definition interp_int32 (v: Value) : Prop :=
  exists z, v = vint32 z.

(** Function type: v must be a closure, and for any arg satisfying A, the body
    evaluated with arg prepended to the closure's environment satisfies B(arg)
    at any fuel level. *)
Definition interp_fun (A: SemTy) (B: Value -> SemTy) (v: Value) : Prop :=
  exists venv' body,
    v = vabs venv' body /\
    forall arg, A arg -> term_has_semtype (arg::venv') body (B arg).

(** Universal type: v must be a type abstraction, and for any semantic type A
    between lower bound L and upper bound U, the body evaluated in the
    closure's environment satisfies F(A) at any fuel level. *)
Definition interp_forall (L U: SemTy) (F: SemTy -> SemTy) (v: Value) : Prop :=
  exists env body,
    v = vtabs env body /\
    forall A,
      (forall w, L w -> A w) ->
      (forall w, A w -> U w) ->
      term_has_semtype env body (F A).

Definition eval_to_true (venv: list Value) (t: Term) : Prop :=
  term_has_semtype venv t (fun v => v = vbool true).

(** Refinement type: v satisfies A and the predicate p evaluates to true
    when v is prepended to the environment. *)
Definition interp_refine (A: SemTy) (p: Term) (venv: list Value) (v: Value) : Prop :=
  A v /\ eval_to_true (v::venv) p.

(** Sigma type (dependent pair): v is a pair (v1, v2) where v1 satisfies A
    and v2 satisfies B(v1). *)
Definition interp_sigma (A: SemTy) (B: Value -> SemTy) (v: Value) : Prop :=
  exists v1 v2, v = vpair v1 v2 /\ A v1 /\ B v1 v2.

(** Sum type: v is an injection (left or right) with the inner value satisfying
    the corresponding type. *)
Definition interp_sum (A B: SemTy) (v: Value) : Prop :=
  (exists w, v = vinl w /\ A w) \/ (exists w, v = vinr w /\ B w).

(** Union type: v satisfies A or B. *)
Definition interp_or (A B: SemTy) (v: Value) : Prop :=
  A v \/ B v.

(** Intersection type: v satisfies A and B. *)
Definition interp_and (A B: SemTy) (v: Value) : Prop :=
  A v /\ B v.

(** Top type: every value satisfies it. *)
Definition interp_top (v: Value)  : Prop := True.

(** Bottom type: no value satisfies it. *)
Definition interp_bot (v: Value)  : Prop := False.

(** Step-indexed interpretation for recursive types.
    At step 0, any value qualifies.
    At step S j, the value must satisfy F applied to the (j-step) approximation. *)
Fixpoint interp_mu (j: nat) (F: SemTy -> SemTy) (v: Value) : Prop :=
  match j with
  | 0 => True
  | S j' => F (interp_mu j' F) v
  end.

(** ** Main interpretation function *)

Fixpoint interp (tvars: list SemTy) (venv: list Value) (T: Ty) : SemTy :=
  match T with
  | TVar i => interp_var tvars i
  | TUnit => interp_unit
  | TBool => interp_bool
  | TInt32 => interp_int32
  | TFun A B => interp_fun (interp tvars venv A) (fun arg => interp tvars (arg::venv) B)
  | TForall L U B => interp_forall (interp tvars venv L) (interp tvars venv U) (fun A => interp (A::tvars) venv B)
  | TRefine A p => interp_refine (interp tvars venv A) p venv
  | TOr A B => interp_or (interp tvars venv A) (interp tvars venv B)
  | TAnd A B => interp_and (interp tvars venv A) (interp tvars venv B)
  | TSigma A B => interp_sigma (interp tvars venv A) (fun v1 => interp tvars (v1::venv) B)
  | TSum A B => interp_sum (interp tvars venv A) (interp tvars venv B)
  | TMuAll B => fun v => forall n, interp_mu n (fun X => interp (X::tvars) venv B) v
  | TTop => interp_top
  | TBot => interp_bot
  end.

(** interp_mu is extensional in F *)
Lemma interp_mu_eq_ext: forall n (F1 F2 : SemTy -> SemTy),
  (forall X v, F1 X v <-> F2 X v) ->
  forall v, interp_mu n F1 v <-> interp_mu n F2 v.
Proof.
  induction n; intros F1 F2 Hext v; simpl.
  - tauto.
  - assert (Heq_mu: interp_mu n F1 = interp_mu n F2).
    { apply functional_extensionality. intro w.
      apply propositional_extensionality. apply IHn. exact Hext. }
    assert (Heq_F: forall X, F1 X = F2 X).
    { intro X. apply functional_extensionality. intro w.
      apply propositional_extensionality. apply Hext. }
    rewrite Heq_mu, Heq_F. tauto.
Qed.

Hint Unfold interp_var interp_unit interp_bool interp_int32 interp_fun interp_forall interp_refine interp_sigma interp_sum interp_or interp_and interp_top interp_bot: core.
