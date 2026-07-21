(** * Substitution Tests

    Executable unit tests ([Example]s proved by [reflexivity]) pinning down
    the behaviour of renaming and substitution on representative cases,
    in particular how they propagate into refinement predicates and type
    annotations. *)

Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.

(** ** Renaming examples *)

(** Shift type variables by 1 in a type. *)
Example ren_ty_shift_tvar :
  ren_ty S id (TVar 0) = TVar 1.
Proof. reflexivity. Qed.

(** Shift term variables by 1 in a term. *)
Example ren_tm_shift_tmvar :
  ren_tm id S (tvar 0) = tvar 1.
Proof. reflexivity. Qed.

(** Type renaming does not affect term variables. *)
Example ren_ty_preserves_tmvar :
  ren_tm S id (tvar 0) = tvar 0.
Proof. reflexivity. Qed.

(** Term renaming does not affect type variables. *)
Example ren_tm_preserves_tyvar :
  ren_ty id S (TVar 0) = TVar 0.
Proof. reflexivity. Qed.

(** Type renaming goes under TForall with upren. *)
Example ren_ty_forall :
  ren_ty S id (TForall TBot TTop (TVar 0)) = TForall TBot TTop (TVar 0).
Proof. reflexivity. Qed.

Example ren_ty_forall_free :
  ren_ty S id (TForall TBot TTop (TVar 1)) = TForall TBot TTop (TVar 2).
Proof. reflexivity. Qed.

(** Term renaming goes under TRefine's predicate. *)
Example ren_tm_refine_bound :
  ren_ty id S (TRefine TBool (tvar 0)) = TRefine TBool (tvar 0).
Proof. reflexivity. Qed.

Example ren_tm_refine_free :
  ren_ty id S (TRefine TBool (tvar 1)) = TRefine TBool (tvar 2).
Proof. reflexivity. Qed.

(** Type renaming propagates into predicates in TRefine. *)
Example ren_ty_refine_propagates :
  ren_ty S id (TRefine TBool (ttapp (tvar 0) (TVar 0))) =
  TRefine TBool (ttapp (tvar 0) (TVar 1)).
Proof. reflexivity. Qed.

(** Term renaming propagates into type annotations in tabs. *)
Example ren_tm_tabs_annotation :
  ren_tm id S (tabs (TRefine TBool (tvar 1)) (tvar 0)) =
  tabs (TRefine TBool (tvar 2)) (tvar 0).
Proof. reflexivity. Qed.

(** ** Substitution examples *)

(** Basic type variable substitution. *)
Example subst_ty_basic :
  subst_ty (TInt32 .: TVar) tvar (TVar 0) = TInt32.
Proof. reflexivity. Qed.

(** Non-target type variable left alone. *)
Example subst_ty_other_var :
  subst_ty (TInt32 .: TVar) tvar (TVar 1) = TVar 0.
Proof. reflexivity. Qed.

(** Type substitution under TForall: bound variable preserved. *)
Example subst_ty_forall_bound :
  subst_ty (TInt32 .: TVar) tvar (TForall TBot TTop (TVar 0)) = TForall TBot TTop (TVar 0).
Proof. reflexivity. Qed.

(** Type substitution under TForall: free variable substituted. *)
Example subst_ty_forall_free :
  subst_ty (TInt32 .: TVar) tvar (TForall TBot TTop (TVar 1)) = TForall TBot TTop TInt32.
Proof. reflexivity. Qed.

(** Type substitution under TForall: free variable shifted. *)
Example subst_ty_forall_free_shift :
  subst_ty (TVar 1 .: TVar) tvar (TForall TBot TTop (TVar 1)) = TForall TBot TTop (TVar 2).
Proof. reflexivity. Qed.

(** KEY TEST: Type substitution propagates into TRefine predicates. *)
Example subst_ty_refine_propagates :
  subst_ty (TInt32 .: TVar) tvar (TRefine TBool (ttapp (tvar 0) (TVar 0))) =
  TRefine TBool (ttapp (tvar 0) TInt32).
Proof. reflexivity. Qed.

(** KEY TEST: Term substitution propagates into type annotations in tabs. *)
Example subst_tm_tabs_annotation :
  subst_tm TVar (tunit .: tvar) (tabs (TRefine TBool (tvar 1)) (tvar 0)) =
  tabs (TRefine TBool tunit) (tvar 0).
Proof. reflexivity. Qed.

(** Term substitution under TRefine: bound variable preserved. *)
Example subst_tm_refine_bound :
  subst_ty TVar (tunit .: tvar) (TRefine TBool (tvar 0)) =
  TRefine TBool (tvar 0).
Proof. reflexivity. Qed.

(** Term substitution under TRefine: free variable substituted. *)
Example subst_tm_refine_free :
  subst_ty TVar (tunit .: tvar) (TRefine TBool (tvar 1)) =
  TRefine TBool tunit.
Proof. reflexivity. Qed.

(** ** ty_subst examples *)

(** ty_subst replaces type var 0. *)
Example ty_subst_basic :
  ty_subst (TVar 0) TInt32 = TInt32.
Proof. reflexivity. Qed.

(** ty_subst propagates into TRefine predicates. *)
Example ty_subst_refine_propagates :
  ty_subst (TRefine TBool (ttapp (tvar 0) (TVar 0))) TInt32 =
  TRefine TBool (ttapp (tvar 0) TInt32).
Proof. reflexivity. Qed.

(** KEY TEST: ty_subst correctly shifts term variables when going under
    TFun's term binder. *)
Example ty_subst_shifts_under_tfun :
  ty_subst (TFun (TVar 0) (TVar 0)) (TRefine TBool (tvar 1)) =
  TFun (TRefine TBool (tvar 1)) (TRefine TBool (tvar 2)).
Proof. reflexivity. Qed.

(** ** Identity substitution *)

Example subst_ty_id :
  subst_ty TVar tvar (TFun (TVar 0) (TRefine TBool (tvar 0))) =
  TFun (TVar 0) (TRefine TBool (tvar 0)).
Proof. reflexivity. Qed.

Example subst_tm_id :
  subst_tm TVar tvar (tabs (TRefine TBool (tvar 0)) (tvar 0)) =
  tabs (TRefine TBool (tvar 0)) (tvar 0).
Proof. reflexivity. Qed.

(** ** Cross-sort independence *)

(** Type substitution does not affect term variables. *)
Example subst_ty_preserves_tmvar :
  subst_ty (TInt32 .: TVar) tvar (TRefine TBool (tvar 0)) =
  TRefine TBool (tvar 0).
Proof. reflexivity. Qed.

(** Term substitution does not affect type variables. *)
Example subst_tm_preserves_tyvar :
  subst_ty TVar (tunit .: tvar) (TForall TBot TTop (TVar 0)) =
  TForall TBot TTop (TVar 0).
Proof. reflexivity. Qed.
