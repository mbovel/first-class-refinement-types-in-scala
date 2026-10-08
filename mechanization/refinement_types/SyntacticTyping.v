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
Require Import RefinementTypes.Avoid.
Require Import RefinementTypes.FirstOrder.
Require Import RefinementTypes.SyntacticSubtyping.
Require Import RefinementTypes.SemanticSubtyping.

Inductive syn_typed (gamma: Ctx) : Term -> Ty -> Prop :=

  | ST_Diverge : forall T,
      syn_typed gamma tdiverge T

  | ST_Unit :
      syn_typed gamma tunit TUnit

  | ST_Bool : forall b,
      syn_typed gamma (tbool b) TBool

  | ST_Int32 : forall z,
      syn_typed gamma (tint32 z) TInt32

  | ST_Var : forall i T,
      nth_error (ctx_tenv gamma) i = Some T ->
      syn_typed gamma (tvar i) (subst_ty TVar (tm_shift (S i)) T)

  | ST_Abs : forall A b B,
      syn_typed (ctx_cons_term gamma A) b B ->
      syn_typed gamma (tabs A b) (TFun A B)

  | ST_App : forall fn i A B,
      syn_typed gamma fn (TFun A B) ->
      syn_typed gamma (tvar i) A ->
      syn_typed gamma (tapp fn (tvar i)) (subst_ty TVar (tvar i .: tvar) B)

  | ST_TAbs : forall L U b A,
      syn_typed (ctx_cons_type gamma L U) b A ->
      syn_typed gamma (ttabs L U b) (TForall L U A)

  | ST_TApp : forall fn L U A B,
      syn_typed gamma fn (TForall L U B) ->
      sem_subtype gamma L A ->
      sem_subtype gamma A U ->
      syn_typed gamma (ttapp fn A) (ty_subst B A)

  | ST_Let : forall e A b B z,
      syn_typed gamma e A ->
      syn_typed (ctx_add_fact (ctx_cons_term gamma A) ((S (ctx_len gamma), tvar 0), (ctx_len gamma, e))) b B ->
      syn_typed gamma (tlet A e b) (subst_ty TVar (z .: tvar) (avoid_var0 B))

  | ST_BinOp : forall op a b T,
      syn_typed gamma a T ->
      syn_typed gamma b T ->
      bin_op_ty_compat op T = true ->
      syn_typed gamma (tbin_op op a b) (bin_op_result_ty op T)

  | ST_If : forall c t e T1 T2,
      syn_typed gamma c TBool ->
      syn_typed (ctx_add_fact gamma ((ctx_len gamma, c), (ctx_len gamma, tbool true))) t T1 ->
      syn_typed (ctx_add_fact gamma ((ctx_len gamma, c), (ctx_len gamma, tbool false))) e T2 ->
      syn_typed gamma (tif c t e) (TOr T1 T2)

  | ST_Loop : forall a A body B,
      ren_ty id S A = A ->
      ren_ty id S B = B ->
      syn_typed gamma a A ->
      syn_typed (ctx_cons_term gamma A) body (TSum A B) ->
      syn_typed gamma (tloop a body) B

  | ST_Selfify : forall e T,
      syn_typed gamma e T ->
      fo T = true ->
      syn_typed gamma e (TRefine T (tbin_op OpEq (tvar 0) (ren_tm id S e)))

  | ST_Sub : forall t A B,
      syn_typed gamma t A ->
      syn_subtype gamma A B ->
      syn_typed gamma t B

  | ST_Pair : forall i e2 A B,
      syn_typed gamma (tvar i) A ->
      syn_typed gamma e2 B ->
      syn_typed gamma (tpair (tvar i) e2) (TSigma A (subst_ty TVar (abstract_term_var i) B))

  | ST_MatchPair : forall e A B body C z1 z2,
      syn_typed gamma e (TSigma A B) ->
      syn_typed (ctx_cons_term (ctx_cons_term gamma A) B) body C ->
      syn_typed gamma (tmatch_pair e body)
        (subst_ty TVar (z2 .: tvar) (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C))))

  | ST_Inl : forall e A B,
      syn_typed gamma e A ->
      syn_typed gamma (tinl B e) (TSum A B)

  | ST_Inr : forall e A B,
      syn_typed gamma e B ->
      syn_typed gamma (tinr A e) (TSum A B)

  | ST_MatchSum : forall e A B body_l body_r C1 C2 zl zr,
      syn_typed gamma e (TSum A B) ->
      syn_typed (ctx_add_fact (ctx_cons_term gamma A) ((ctx_len gamma, e), (S (ctx_len gamma), tinl B (tvar 0))))
        body_l C1 ->
      syn_typed (ctx_add_fact (ctx_cons_term gamma B) ((ctx_len gamma, e), (S (ctx_len gamma), tinr A (tvar 0))))
        body_r C2 ->
      syn_typed gamma (tmatch_sum e body_l body_r)
        (TOr (subst_ty TVar (zl .: tvar) (avoid_var0 C1))
             (subst_ty TVar (zr .: tvar) (avoid_var0 C2))).
