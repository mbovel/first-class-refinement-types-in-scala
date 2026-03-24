(** * Syntactic Subtyping

    Inductive subtyping judgment mirroring the semantic subtyping rules. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.WfLemmas.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.SemanticImplies.

Inductive syn_subtype (tbounds: TBounds) (tenv: list Ty)
  (facts: list ((nat * Term) * (nat * Term))) : Ty -> Ty -> Prop :=

  | SSub_Refl : forall A,
      syn_subtype tbounds tenv facts A A

  | SSub_Trans : forall A B C,
      syn_subtype tbounds tenv facts A B ->
      syn_subtype tbounds tenv facts B C ->
      syn_subtype tbounds tenv facts A C

  | SSub_Fun : forall A1 A2 B1 B2,
      syn_subtype tbounds tenv facts B1 A1 ->
      syn_subtype (tbounds_shift_term tbounds) (A1 :: tenv) facts A2 B2 ->
      syn_subtype tbounds tenv facts (TFun A1 A2) (TFun B1 B2)

  | SSub_Forall : forall L1 U1 L2 U2 A B,
      syn_subtype tbounds tenv facts L1 L2 ->
      syn_subtype tbounds tenv facts U2 U1 ->
      syn_subtype ((L2, U2) :: tbounds) (tenv_shift_type tenv) facts A B ->
      syn_subtype tbounds tenv facts (TForall L1 U1 A) (TForall L2 U2 B)

  | SSub_Sigma : forall A1 A2 B1 B2,
      syn_subtype tbounds tenv facts A1 B1 ->
      syn_subtype (tbounds_shift_term tbounds) (A1 :: tenv) facts A2 B2 ->
      syn_subtype tbounds tenv facts (TSigma A1 A2) (TSigma B1 B2)

  | SSub_Or_L : forall A B,
      syn_subtype tbounds tenv facts A (TOr A B)

  | SSub_Or_R : forall A B,
      syn_subtype tbounds tenv facts B (TOr A B)

  | SSub_Or : forall A B C,
      syn_subtype tbounds tenv facts A C ->
      syn_subtype tbounds tenv facts B C ->
      syn_subtype tbounds tenv facts (TOr A B) C

  | SSub_And_L : forall A B,
      syn_subtype tbounds tenv facts (TAnd A B) A

  | SSub_And_R : forall A B,
      syn_subtype tbounds tenv facts (TAnd A B) B

  | SSub_And : forall A B C,
      syn_subtype tbounds tenv facts C A ->
      syn_subtype tbounds tenv facts C B ->
      syn_subtype tbounds tenv facts C (TAnd A B)

  | SSub_Refine_Base : forall A p,
      syn_subtype tbounds tenv facts (TRefine A p) A

  | SSub_Refine : forall A B p1 p2,
      syn_subtype tbounds tenv facts A B ->
      sem_implies (tbounds_shift_term tbounds) (A :: tenv) facts p1 p2 ->
      syn_subtype tbounds tenv facts (TRefine A p1) (TRefine B p2)

  | SSub_Top : forall A,
      syn_subtype tbounds tenv facts A TTop

  | SSub_Bot : forall A,
      syn_subtype tbounds tenv facts TBot A

  | SSub_TVar_Upper : forall i L U,
      nth_error tbounds i = Some (L, U) ->
      syn_subtype tbounds tenv facts (TVar i) (ren_ty (fun n => n + S i) id U)

  | SSub_TVar_Lower : forall i L U,
      nth_error tbounds i = Some (L, U) ->
      syn_subtype tbounds tenv facts (ren_ty (fun n => n + S i) id L) (TVar i)

  | SSub_Mu_Unfold : forall A,
      spos 0 A = true ->
      syn_subtype tbounds tenv facts (TMuAll A) (ty_subst A (TMuAll A))

  | SSub_Mu_Fold : forall A,
      spos 0 A = true ->
      syn_subtype tbounds tenv facts (ty_subst A (TMuAll A)) (TMuAll A).
