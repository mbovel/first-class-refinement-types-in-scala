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

Inductive syn_typed (G: Ctx) : Term -> Ty -> Prop :=

  | ST_Diverge : forall T,
      syn_typed G tdiverge T

  | ST_Unit :
      syn_typed G tunit TUnit

  | ST_Bool : forall b,
      syn_typed G (tbool b) TBool

  | ST_Int32 : forall z,
      syn_typed G (tint32 z) TInt32

  | ST_Var : forall i T,
      nth_error (ctx_tenv G) i = Some T ->
      syn_typed G (tvar i) (subst_ty TVar (tm_shift (S i)) T)

  | ST_Abs : forall A b B,
      syn_typed (ctx_cons_term G A) b B ->
      syn_typed G (tabs A b) (TFun A B)

  | ST_App : forall fn i A B,
      syn_typed G fn (TFun A B) ->
      syn_typed G (tvar i) A ->
      syn_typed G (tapp fn (tvar i)) (subst_ty TVar (tvar i .: tvar) B)

  | ST_TAbs : forall L U b A,
      syn_typed (ctx_cons_type G L U) b A ->
      syn_typed G (ttabs L U b) (TForall L U A)

  | ST_TApp : forall fn L U A B,
      syn_typed G fn (TForall L U B) ->
      sem_subtype G L A ->
      sem_subtype G A U ->
      syn_typed G (ttapp fn A) (ty_subst B A)

  | ST_Let : forall e A b B z,
      syn_typed G e A ->
      syn_typed (ctx_add_fact (ctx_cons_term G A) ((S (ctx_len G), tvar 0), (ctx_len G, e))) b B ->
      syn_typed G (tlet A e b) (subst_ty TVar (z .: tvar) (avoid_var0 B))

  | ST_BinOp : forall op a b T,
      syn_typed G a T ->
      syn_typed G b T ->
      bin_op_ty_compat op T = true ->
      syn_typed G (tbin_op op a b) (bin_op_result_ty op T)

  | ST_If : forall c t e T1 T2,
      syn_typed G c TBool ->
      syn_typed (ctx_add_fact G ((ctx_len G, c), (ctx_len G, tbool true))) t T1 ->
      syn_typed (ctx_add_fact G ((ctx_len G, c), (ctx_len G, tbool false))) e T2 ->
      syn_typed G (tif c t e) (TOr T1 T2)

  | ST_Loop : forall a A body B,
      ren_ty id S A = A ->
      ren_ty id S B = B ->
      syn_typed G a A ->
      syn_typed (ctx_cons_term G A) body (TSum A B) ->
      syn_typed G (tloop a body) B

  | ST_Selfify : forall e T,
      syn_typed G e T ->
      fo T = true ->
      syn_typed G e (TRefine T (tbin_op OpEq (tvar 0) (ren_tm id S e)))

  | ST_Sub : forall t A B,
      syn_typed G t A ->
      syn_subtype G A B ->
      syn_typed G t B

  | ST_Pair : forall i e2 A B,
      syn_typed G (tvar i) A ->
      syn_typed G e2 B ->
      syn_typed G (tpair (tvar i) e2) (TSigma A (subst_ty TVar (abstract_term_var i) B))

  | ST_MatchPair : forall e A B body C z1 z2,
      syn_typed G e (TSigma A B) ->
      syn_typed (ctx_cons_term (ctx_cons_term G A) B) body C ->
      syn_typed G (tmatch_pair e body)
        (subst_ty TVar (z2 .: tvar) (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C))))

  | ST_Inl : forall e A B,
      syn_typed G e A ->
      syn_typed G (tinl B e) (TSum A B)

  | ST_Inr : forall e A B,
      syn_typed G e B ->
      syn_typed G (tinr A e) (TSum A B)

  | ST_MatchSum : forall e A B body_l body_r C1 C2 zl zr,
      syn_typed G e (TSum A B) ->
      syn_typed (ctx_add_fact (ctx_cons_term G A) ((ctx_len G, e), (S (ctx_len G), tinl B (tvar 0))))
        body_l C1 ->
      syn_typed (ctx_add_fact (ctx_cons_term G B) ((ctx_len G, e), (S (ctx_len G), tinr A (tvar 0))))
        body_r C2 ->
      syn_typed G (tmatch_sum e body_l body_r)
        (TOr (subst_ty TVar (zl .: tvar) (avoid_var0 C1))
             (subst_ty TVar (zr .: tvar) (avoid_var0 C2))).
