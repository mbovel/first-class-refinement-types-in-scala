From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import ZArith.BinInt.
Require Import RefinementTypes.Syntax.

(** Signed 32-bit wrapping: maps any Z to the range [-2^31, 2^31). *)
Definition int32_wrap (z : Z) : Z :=
  ((z + 2^31) mod 2^32 - 2^31)%Z.

(** Evaluate a binary operation on two values.
    Returns [Some v] if the operation is defined, [None] otherwise.
    For equality/inequality, heterogeneous comparisons on first-order values
    return [Some (vbool false)]/[Some (vbool true)]; closures return [None]. *)
Definition eval_bin_op (op: BinOp) (v1 v2: Value) : option Value :=
  match op, v1, v2 with
  (* Equality *)
  | OpEq, vunit, vunit => Some (vbool true)
  | OpEq, vunit, _ => Some (vbool false)
  | OpEq, vbool b1, vbool b2 => Some (vbool (Bool.eqb b1 b2))
  | OpEq, vbool _, _ => Some (vbool false)
  | OpEq, vint32 z1, vint32 z2 => Some (vbool (Z.eqb z1 z2))
  | OpEq, vint32 _, _ => Some (vbool false)
  (* Inequality *)
  | OpNeq, vunit, vunit => Some (vbool false)
  | OpNeq, vunit, _ => Some (vbool true)
  | OpNeq, vbool b1, vbool b2 => Some (vbool (negb (Bool.eqb b1 b2)))
  | OpNeq, vbool _, _ => Some (vbool true)
  | OpNeq, vint32 z1, vint32 z2 => Some (vbool (negb (Z.eqb z1 z2)))
  | OpNeq, vint32 _, _ => Some (vbool true)
  (* Less than *)
  | OpLt, vint32 z1, vint32 z2 => Some (vbool (Z.ltb z1 z2))
  (* Less or equal *)
  | OpLe, vint32 z1, vint32 z2 => Some (vbool (Z.leb z1 z2))
  (* Greater or equal *)
  | OpGe, vint32 z1, vint32 z2 => Some (vbool (Z.leb z2 z1))
  (* Greater than *)
  | OpGt, vint32 z1, vint32 z2 => Some (vbool (Z.ltb z2 z1))
  (* Logical and *)
  | OpAnd, vbool b1, vbool b2 => Some (vbool (andb b1 b2))
  (* Logical or *)
  | OpOr, vbool b1, vbool b2 => Some (vbool (orb b1 b2))
  (* Arithmetic: addition *)
  | OpAdd, vint32 z1, vint32 z2 => Some (vint32 (int32_wrap (z1 + z2)))
  (* Arithmetic: subtraction *)
  | OpSub, vint32 z1, vint32 z2 => Some (vint32 (int32_wrap (z1 - z2)))
  (* Arithmetic: multiplication *)
  | OpMul, vint32 z1, vint32 z2 => Some (vint32 (int32_wrap (z1 * z2)))
  (* Arithmetic: division *)
  | OpDiv, vint32 z1, vint32 z2 => Some (vint32 (int32_wrap (z1 / z2)))
  (* Arithmetic: modulo *)
  | OpMod, vint32 z1, vint32 z2 => Some (vint32 (int32_wrap (Z.modulo z1 z2)))
  (* Everything else *)
  | _, _, _ => None
  end.

(** A first-order value is unit, a boolean, or an integer. *)
Definition fo_val (v: Value) : Prop :=
  v = vunit \/ (exists b, v = vbool b) \/ (exists z, v = vint32 z).

(** Value-level predicate: eval_bin_op is defined when values are compatible. *)
Definition bin_op_val_pair_compat (op: BinOp) (va vb: Value) : Prop :=
  match op with
  | OpEq | OpNeq => fo_val va /\ fo_val vb
  | OpLt | OpLe | OpGe | OpGt | OpAdd | OpSub | OpMul | OpDiv | OpMod =>
      exists z1 z2, va = vint32 z1 /\ vb = vint32 z2
  | OpAnd | OpOr =>
      exists b1 b2, va = vbool b1 /\ vb = vbool b2
  end.

(** Loop runner: iterate [step] up to [fuel] times.
    Returns the first [vinr v] result unwrapped (break), recurs on [vinl v] (continue),
    or gets stuck on any other value. *)
Fixpoint run_loop (step : Value -> option (option Value)) (fuel : nat) (va : Value)
  : option (option Value) :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match step va with
    | None => None
    | Some None => Some None
    | Some (Some (vinr v)) => Some (Some v)
    | Some (Some (vinl v)) => run_loop step fuel' v
    | Some (Some _) => Some None
    end
  end.

(**
Fuel-based big-step evaluator for terms.

The result is a layered option type:
- [None]             means timeout (ran out of fuel)
- [Some None]        means stuck (runtime error)
- [Some (Some v)]    means successful evaluation to value [v]

The layered approach simplifies proofs compared to using a single sum type
*)
Fixpoint eval (fuel: nat) (env: list Value) (t: Term) : option (option Value) :=
  match fuel with
  | 0 => None
  | S fuel =>
    match t with
    | tunit => Some (Some vunit)
    | tbool b => Some (Some (vbool b))
    | tint32 z => Some (Some (vint32 z))
    | tvar i =>
        match nth_error env i with
        | None => Some None
        | Some v => Some (Some v)
        end
    | tabs A b => Some (Some (vabs env b))
    | ttabs _ _ b => Some (Some (vtabs env b))
    | tapp f a =>
        match eval fuel env f with
        | None => None
        | Some (Some (vabs envf b)) =>
            match eval fuel env a with
            | None => None
            | Some None => Some None
            | Some (Some va) => eval fuel (va :: envf) b
            end
        | _ => Some None
        end
    | ttapp f _ =>
        match eval fuel env f with
        | None => None
        | Some (Some (vtabs envf b)) =>
            eval fuel envf b
        | _ => Some None
        end
    | tlet _ e b =>
        match eval fuel env e with
        | None => None
        | Some None => Some None
        | Some (Some v) => eval fuel (v :: env) b
        end
    | tpair e1 e2 =>
        match eval fuel env e1 with
        | None => None
        | Some None => Some None
        | Some (Some v1) =>
            match eval fuel env e2 with
            | None => None
            | Some None => Some None
            | Some (Some v2) => Some (Some (vpair v1 v2))
            end
        end
    | tmatch_pair e body =>
        match eval fuel env e with
        | None => None
        | Some (Some (vpair v1 v2)) => eval fuel (v2 :: v1 :: env) body
        | _ => Some None
        end
    | tinl _ e =>
        match eval fuel env e with
        | None => None
        | Some None => Some None
        | Some (Some v) => Some (Some (vinl v))
        end
    | tinr _ e =>
        match eval fuel env e with
        | None => None
        | Some None => Some None
        | Some (Some v) => Some (Some (vinr v))
        end
    | tmatch_sum e body_l body_r =>
        match eval fuel env e with
        | None => None
        | Some (Some (vinl v)) => eval fuel (v :: env) body_l
        | Some (Some (vinr v)) => eval fuel (v :: env) body_r
        | _ => Some None
        end
    | tbin_op op a b =>
        match eval fuel env a with
        | None => None
        | Some None => Some None
        | Some (Some va) =>
            match eval fuel env b with
            | None => None
            | Some None => Some None
            | Some (Some vb) =>
                match eval_bin_op op va vb with
                | Some v => Some (Some v)
                | None => Some None  (* not comparable: stuck *)
                end
            end
        end
    | tif c t e =>
        match eval fuel env c with
        | None => None
        | Some None => Some None
        | Some (Some (vbool true)) => eval fuel env t
        | Some (Some (vbool false)) => eval fuel env e
        | _ => Some None  (* condition not a boolean: stuck *)
        end
    | tdiverge => None  (* diverging term: always loops *)
    | tloop a body =>
        match eval fuel env a with
        | None => None
        | Some None => Some None
        | Some (Some va) =>
            run_loop (fun v => eval fuel (v :: env) body) fuel va
        end
    end
  end.
