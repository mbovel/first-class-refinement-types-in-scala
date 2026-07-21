(** * Syntactic Typing (Figure 9)

    Inductive typing judgment Γ ⊢ a : A mirroring the semantic typing
    rules; each constructor corresponds to a rule of Figure 9 and to the
    lemma of the same name in [SemanticTyping]. Adequacy — the syntactic
    judgment implies the semantic one — is Theorem 3.1, proved in
    [Adequacy]. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.WfLemmas.
Require Import RefinementTypes.Avoid.
Require Import RefinementTypes.FirstOrder.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.SyntacticSubtyping.
Require Import RefinementTypes.SemanticSubtyping.
Require Import RefinementTypes.SemanticImplies.

Inductive syn_typed (tbounds: TBounds) (tenv: list Ty)
  (facts: list ((nat * Term) * (nat * Term))) : Term -> Ty -> Prop :=

  | ST_Diverge : forall T,
      syn_typed tbounds tenv facts tdiverge T

  | ST_Unit :
      syn_typed tbounds tenv facts tunit TUnit

  | ST_Bool : forall b,
      syn_typed tbounds tenv facts (tbool b) TBool

  | ST_Int32 : forall z,
      syn_typed tbounds tenv facts (tint32 z) TInt32

  | ST_Var : forall i T,
      nth_error tenv i = Some T ->
      syn_typed tbounds tenv facts (tvar i) (subst_ty TVar (tm_shift (S i)) T)

  | ST_Abs : forall A b B,
      syn_typed (tbounds_shift_term tbounds) (A :: tenv) facts b B ->
      syn_typed tbounds tenv facts (tabs A b) (TFun A B)

  | ST_App : forall fn i A B,
      syn_typed tbounds tenv facts fn (TFun A B) ->
      syn_typed tbounds tenv facts (tvar i) A ->
      syn_typed tbounds tenv facts (tapp fn (tvar i)) (subst_ty TVar (tvar i .: tvar) B)

  | ST_TAbs : forall L U b A,
      syn_typed ((L, U) :: tbounds) (tenv_shift_type tenv) facts b A ->
      syn_typed tbounds tenv facts (ttabs L U b) (TForall L U A)

  | ST_TApp : forall fn L U A B,
      syn_typed tbounds tenv facts fn (TForall L U B) ->
      sem_subtype tbounds tenv facts L A ->
      sem_subtype tbounds tenv facts A U ->
      syn_typed tbounds tenv facts (ttapp fn A) (ty_subst B A)

  | ST_Let : forall e A b B z,
      syn_typed tbounds tenv facts e A ->
      syn_typed (tbounds_shift_term tbounds) (A :: tenv)
        (((S (length tenv), tvar 0), (length tenv, e)) :: facts) b B ->
      syn_typed tbounds tenv facts (tlet A e b)
        (subst_ty TVar (z .: tvar) (avoid_var0 B))

  | ST_BinOp : forall op a b T,
      syn_typed tbounds tenv facts a T ->
      syn_typed tbounds tenv facts b T ->
      bin_op_ty_compat op T = true ->
      syn_typed tbounds tenv facts (tbin_op op a b) (bin_op_result_ty op T)

  | ST_If : forall c t e T1 T2,
      syn_typed tbounds tenv facts c TBool ->
      syn_typed tbounds tenv
        (((length tenv, c), (length tenv, tbool true)) :: facts) t T1 ->
      syn_typed tbounds tenv
        (((length tenv, c), (length tenv, tbool false)) :: facts) e T2 ->
      syn_typed tbounds tenv facts (tif c t e) (TOr T1 T2)

  | ST_Loop : forall a A body B,
      ren_ty id S A = A ->
      ren_ty id S B = B ->
      syn_typed tbounds tenv facts a A ->
      syn_typed (tbounds_shift_term tbounds) (A :: tenv) facts body (TSum A B) ->
      syn_typed tbounds tenv facts (tloop a body) B

  | ST_Selfify : forall e T,
      syn_typed tbounds tenv facts e T ->
      fo T = true ->
      syn_typed tbounds tenv facts e (TRefine T (tbin_op OpEq (tvar 0) (ren_tm id S e)))

  | ST_Sub : forall t A B,
      syn_typed tbounds tenv facts t A ->
      syn_subtype tbounds tenv facts A B ->
      syn_typed tbounds tenv facts t B

  | ST_Pair : forall i e2 A B,
      syn_typed tbounds tenv facts (tvar i) A ->
      syn_typed tbounds tenv facts e2 B ->
      syn_typed tbounds tenv facts (tpair (tvar i) e2)
        (TSigma A (subst_ty TVar (abstract_term_var i) B))

  | ST_MatchPair : forall e A B body C z1 z2,
      syn_typed tbounds tenv facts e (TSigma A B) ->
      syn_typed (tbounds_shift_term (tbounds_shift_term tbounds)) (B :: A :: tenv) facts body C ->
      syn_typed tbounds tenv facts (tmatch_pair e body)
        (subst_ty TVar (z2 .: tvar) (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C))))

  | ST_Inl : forall e A B,
      syn_typed tbounds tenv facts e A ->
      syn_typed tbounds tenv facts (tinl B e) (TSum A B)

  | ST_Inr : forall e A B,
      syn_typed tbounds tenv facts e B ->
      syn_typed tbounds tenv facts (tinr A e) (TSum A B)

  | ST_MatchSum : forall e A B body_l body_r C1 C2 zl zr,
      syn_typed tbounds tenv facts e (TSum A B) ->
      syn_typed (tbounds_shift_term tbounds) (A :: tenv)
        (((length tenv, e), (S (length tenv), tinl B (tvar 0))) :: facts) body_l C1 ->
      syn_typed (tbounds_shift_term tbounds) (B :: tenv)
        (((length tenv, e), (S (length tenv), tinr A (tvar 0))) :: facts) body_r C2 ->
      syn_typed tbounds tenv facts (tmatch_sum e body_l body_r)
        (TOr (subst_ty TVar (zl .: tvar) (avoid_var0 C1))
             (subst_ty TVar (zr .: tvar) (avoid_var0 C2))).
