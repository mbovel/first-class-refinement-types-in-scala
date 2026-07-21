(** * Example: maximum

    Encoding of a polymorphic [maximum] function using a loop over an
    equi-recursive list, with evaluation tests and (partial) typing and
    subtyping derivations. Not presented in the paper. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import ZArith.BinInt.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.WfLemmas.
Require Import RefinementTypes.Avoid.
Require Import RefinementTypes.FirstOrder.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.SyntacticSubtyping.
Require Import RefinementTypes.SyntacticTyping.
Require Import RefinementTypes.SemanticSubtyping.
Require Import RefinementTypes.SemanticImplies.

(** ** Type abbreviations *)

Definition ListTy (tv : nat) : Ty :=
  TMuAll (TSum TUnit (TSigma (TVar (S tv)) (TVar 0))).

Definition OptionTy (tv : nat) : Ty :=
  TSum TUnit (TVar tv).

Definition OrderingTy (tv : nat) : Ty :=
  TFun (TVar tv) (TFun (TVar tv) TBool).

Definition AccTy : Ty := TSigma (ListTy 0) (OptionTy 0).
Definition ResTy : Ty := OptionTy 0.
Definition ListTy_unfolded : Ty := TSum TUnit (TSigma (TVar 0) (ListTy 0)).

(** ** Types and terms *)

Definition maximum_ty : Ty :=
  TForall TBot TTop
    (TForall TBot (TVar 0)
      (TFun (ListTy 0)
        (TFun (OrderingTy 1)
          (OptionTy 0)))).

Definition maximum_tm : Term :=
  ttabs TBot TTop
    (ttabs TBot (TVar 0)
      (tabs (ListTy 0)
        (tabs (OrderingTy 1)
          (tloop
            (tpair (tvar 1) (tinl (TVar 0) tunit))
            (tmatch_pair (tvar 0)
              (tmatch_sum (tvar 1)
                (tinr AccTy (tvar 1))
                (tmatch_pair (tvar 0)
                  (tmatch_sum (tvar 3)
                    (tinl ResTy
                      (tpair (tvar 1) (tinr TUnit (tvar 2))))
                    (tif (tapp (tapp (tvar 7) (tvar 0)) (tvar 2))
                      (tinl ResTy
                        (tpair (tvar 1) (tinr TUnit (tvar 2))))
                      (tinl ResTy
                        (tpair (tvar 1) (tinr TUnit (tvar 0)))))
                  ))
              )))))).

(** ** Evaluation tests *)

Fixpoint list_term (elems : list Term) : Term :=
  match elems with
  | [] => tinl TUnit tunit
  | x :: xs => tinr TUnit (tpair x (list_term xs))
  end.

Definition int_le : Term :=
  tabs TInt32 (tabs TInt32 (tbin_op OpLe (tvar 1) (tvar 0))).

Definition test_maximum_nonempty : Term :=
  tapp (tapp (ttapp (ttapp maximum_tm TInt32) TInt32)
    (list_term (map tint32 [3%Z; 1%Z; 4%Z; 1%Z; 5%Z])))
    int_le.

Compute (eval 1000 [] test_maximum_nonempty).
(* = Some (Some (vinr (vint32 5))) *)

Definition test_maximum_empty : Term :=
  tapp (tapp (ttapp (ttapp maximum_tm TInt32) TInt32)
    (list_term []))
    int_le.

Compute (eval 1000 [] test_maximum_empty).
(* = Some (Some (vinl vunit)) *)

Definition test_maximum_singleton : Term :=
  tapp (tapp (ttapp (ttapp maximum_tm TInt32) TInt32)
    (list_term (map tint32 [42%Z])))
    int_le.

Compute (eval 1000 [] test_maximum_singleton).
(* = Some (Some (vinr (vint32 42))) *)

(** ** Subtyping derivations *)

(** U <: T via upper bound *)
Lemma U_sub_T : forall tbounds tenv facts,
  nth_error tbounds 0 = Some (TBot, TVar 0) ->
  syn_subtype tbounds tenv facts (TVar 0) (TVar 1).
Proof.
  intros * H.
  replace (TVar 1) with (ren_ty (fun n => n + 1) id (TVar 0)) by reflexivity.
  exact (SSub_TVar_Upper _ _ _ 0 TBot (TVar 0) H).
Qed.

Lemma tbounds_shift_term_hd : forall tb,
  nth_error tb 0 = Some (TBot, TVar 0) ->
  nth_error (tbounds_shift_term tb) 0 = Some (TBot, TVar 0).
Proof.
  intros [| [L U] tb'] H; simpl in *; try discriminate.
  injection H as -> ->. reflexivity.
Qed.

(** List unfold: List[U] <: Unit + (U, List[U]) *)
Lemma list_unfold_sub : forall tbounds tenv facts,
  syn_subtype tbounds tenv facts (ListTy 0) ListTy_unfolded.
Proof.
  intros. unfold ListTy, ListTy_unfolded.
  replace (TSum TUnit (TSigma (TVar 0) (TMuAll (TSum TUnit (TSigma (TVar 1) (TVar 0))))))
    with (ty_subst (TSum TUnit (TSigma (TVar 1) (TVar 0)))
                    (TMuAll (TSum TUnit (TSigma (TVar 1) (TVar 0))))) by reflexivity.
  apply SSub_Mu_Unfold. reflexivity.
Qed.

(** Ordering[T] <: Ordering[U] by function contravariance and U <: T *)
Lemma ordering_sub : forall tbounds tenv facts,
  nth_error tbounds 0 = Some (TBot, TVar 0) ->
  syn_subtype tbounds tenv facts (OrderingTy 1) (OrderingTy 0).
Proof.
  intros * Hb. unfold OrderingTy.
  apply SSub_Fun.
  - apply U_sub_T. exact Hb.
  - apply SSub_Fun.
    + apply U_sub_T. apply tbounds_shift_term_hd. exact Hb.
    + apply SSub_Refl.
Qed.

(** TOr T T <: T *)
Lemma or_same_sub : forall tbounds tenv facts T,
  syn_subtype tbounds tenv facts (TOr T T) T.
Proof. intros. apply SSub_Or; apply SSub_Refl. Qed.

(** ** Typing derivation *)

(** Tell [simpl] to always unfold [id]. Without this, [ren_ty id S] leaves
    stray [id] applications in type variable indices. *)
#[global] Arguments id {A} x /.

(** Type a variable by lookup.
    ST_Var produces [subst_ty TVar (tm_shift (S i)) T]; for term-var-free types
    this is convertible to [T], so [change] succeeds. *)
Ltac type_var :=
  match goal with
  | |- syn_typed ?tb ?te ?f (tvar ?i) ?T =>
    change T with (subst_ty TVar (tm_shift (S i)) T);
    exact (ST_Var tb te f i T eq_refl)
  end.

Theorem maximum_typed :
  syn_typed [] [] [] maximum_tm maximum_ty.
Proof.
  unfold maximum_tm, maximum_ty.
  apply ST_TAbs. apply ST_TAbs. apply ST_Abs. apply ST_Abs. simpl.

  (* --- tloop : ResTy --- *)
  eapply ST_Loop with (A := AccTy) (B := ResTy); [reflexivity | reflexivity | | ].

  - (* Initial value: (xs, inl(unit)) : AccTy *)
    unfold AccTy.
    change (TSigma (ListTy 0) (OptionTy 0))
      with (TSigma (ListTy 0) (subst_ty TVar (abstract_term_var 1) (OptionTy 0))).
    eapply ST_Pair.
    + type_var.
    + apply ST_Inl. apply ST_Unit.

  - (* Loop body : TSum AccTy ResTy *)
    (* The body is deeply nested pattern matches. We admit the inner
       derivation for now — the key subtyping lemmas above (U_sub_T,
       list_unfold_sub, ordering_sub, or_same_sub) are the interesting part. *)
    admit.
Admitted.
