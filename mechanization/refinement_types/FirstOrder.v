(** * First-Order Types

    First-order types are types whose values support equality comparison.
    This includes unit, booleans, integers, and refinements over first-order types.
*)

Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.

(** A type is first-order if its values can be compared for equality. *)
Fixpoint fo (T: Ty) : bool :=
  match T with
  | TUnit => true
  | TBool => true
  | TInt32 => true
  | TRefine A _ => fo A
  | TMuAll _ => false
  | _ => false
  end.

(** A type is ordered if its values support comparison (<, <=, >=, >). *)
Fixpoint ordered (T: Ty) : bool :=
  match T with
  | TInt32 => true
  | TRefine A _ => ordered A
  | _ => false
  end.

(** A type is boolean if its values support logical operations (&&, ||). *)
Fixpoint bool_ty (T: Ty) : bool :=
  match T with
  | TBool => true
  | TRefine A _ => bool_ty A
  | _ => false
  end.

(** Strip refinements to get the underlying base type. *)
Fixpoint base_ty (T: Ty) : Ty :=
  match T with
  | TRefine A _ => base_ty A
  | _ => T
  end.

(** Type-level compatibility for binary operations. *)
Definition bin_op_ty_compat (op: BinOp) (T: Ty) : bool :=
  match op with
  | OpEq | OpNeq => fo T
  | OpLt | OpLe | OpGe | OpGt | OpAdd | OpSub | OpMul | OpDiv | OpMod => ordered T
  | OpAnd | OpOr => bool_ty T
  end.

(** Result type of a binary operation. *)
Definition bin_op_result_ty (op: BinOp) (T: Ty) : Ty :=
  match op with
  | OpEq | OpNeq | OpLt | OpLe | OpGe | OpGt | OpAnd | OpOr => TBool
  | OpAdd | OpSub | OpMul | OpDiv | OpMod => base_ty T
  end.
