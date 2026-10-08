(** * Syntactic Subtyping (Figure 10)

    Inductive subtyping judgment Γ ⊢ A <: B mirroring the semantic
    subtyping rules; each constructor corresponds to a rule of Figure 10
    and to the lemma of the same name in [SemanticSubtyping]. Adequacy is
    Theorem 3.2, proved in [Adequacy]. Note that the S-Refine premise uses
    the _semantic_ implication judgment [sem_implies], which has no
    syntactic counterpart. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.SemanticImplies.

Inductive syn_subtype (G: Ctx) : Ty -> Ty -> Prop :=

  | SSub_Refl : forall A,
      syn_subtype G A A

  | SSub_Trans : forall A B C,
      syn_subtype G A B ->
      syn_subtype G B C ->
      syn_subtype G A C

  | SSub_Fun : forall A1 A2 B1 B2,
      syn_subtype G B1 A1 ->
      syn_subtype (ctx_cons_term G A1) A2 B2 ->
      syn_subtype G (TFun A1 A2) (TFun B1 B2)

  | SSub_Forall : forall L1 U1 L2 U2 A B,
      syn_subtype G L1 L2 ->
      syn_subtype G U2 U1 ->
      syn_subtype (ctx_cons_type G L2 U2) A B ->
      syn_subtype G (TForall L1 U1 A) (TForall L2 U2 B)

  | SSub_Sigma : forall A1 A2 B1 B2,
      syn_subtype G A1 B1 ->
      syn_subtype (ctx_cons_term G A1) A2 B2 ->
      syn_subtype G (TSigma A1 A2) (TSigma B1 B2)

  | SSub_Or_L : forall A B,
      syn_subtype G A (TOr A B)

  | SSub_Or_R : forall A B,
      syn_subtype G B (TOr A B)

  | SSub_Or : forall A B C,
      syn_subtype G A C ->
      syn_subtype G B C ->
      syn_subtype G (TOr A B) C

  | SSub_And_L : forall A B,
      syn_subtype G (TAnd A B) A

  | SSub_And_R : forall A B,
      syn_subtype G (TAnd A B) B

  | SSub_And : forall A B C,
      syn_subtype G C A ->
      syn_subtype G C B ->
      syn_subtype G C (TAnd A B)

  | SSub_Refine_Base : forall A p,
      syn_subtype G (TRefine A p) A

  | SSub_Refine : forall A B p1 p2,
      syn_subtype G A B ->
      sem_implies (ctx_cons_term G A) p1 p2 ->
      syn_subtype G (TRefine A p1) (TRefine B p2)

  | SSub_Top : forall A,
      syn_subtype G A TTop

  | SSub_Bot : forall A,
      syn_subtype G TBot A

  | SSub_TVar_Upper : forall i L U,
      nth_error (ctx_tbounds G) i = Some (L, U) ->
      syn_subtype G (TVar i) (ren_ty (fun n => n + S i) id U)

  | SSub_TVar_Lower : forall i L U,
      nth_error (ctx_tbounds G) i = Some (L, U) ->
      syn_subtype G (ren_ty (fun n => n + S i) id L) (TVar i)

  | SSub_Mu_Unfold : forall A,
      spos 0 A = true ->
      syn_subtype G (TMuAll A) (ty_subst A (TMuAll A))

  | SSub_Mu_Fold : forall A,
      spos 0 A = true ->
      syn_subtype G (ty_subst A (TMuAll A)) (TMuAll A).
