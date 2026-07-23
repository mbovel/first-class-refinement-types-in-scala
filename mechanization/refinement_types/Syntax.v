(** * Syntax (Figure 5)

    Abstract syntax of the core calculus. Types and terms are mutually
    inductive, since refinement types [TRefine A p] embed a term [p] as a
    predicate. Bindings use de Bruijn indices.

    Two presentational differences with the paper: Figure 5 has singleton
    base types [True] and [False] where the mechanization uses a single
    [TBool], and the mechanization includes a primitive diverging term
    [tdiverge] while the paper leaves "diverge" informal (any closed term
    that never terminates). *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ZArith.BinInt.

Definition var := nat.

(** ** Binary operations *)
Inductive BinOp :=
  | OpEq | OpNeq                           (* Equality and inequality *)
  | OpLt | OpLe | OpGe | OpGt              (* Ordering comparisons *)
  | OpAnd | OpOr                           (* Logical and/or *)
  | OpAdd | OpSub | OpMul | OpDiv | OpMod. (* Arithmetic operations *)

Lemma bin_op_eq_dec : forall (x y : BinOp), {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** ** Types and terms

    Binding structure (for de Bruijn substitution):
    - TFun A B:       B binds 1 term var
    - TForall L U B:  B binds 1 type var (L, U are not under the binder)
    - TRefine A p:    p binds 1 term var
    - TSigma A B:     B binds 1 term var
    - tabs A b:       b binds 1 term var
    - ttabs L U b:    b binds 1 type var (L, U are not under the binder)
    - tlet A a b:     b binds 1 term var
    - tmatch_pair e b: b binds 2 term vars
    - tmatch_sum e l r: l and r each bind 1 term var
    - tdiverge:        no binders (closed, always diverges)
    - tloop a body:    body binds 1 term var
    - TMuAll B:        B binds 1 type var *)

Inductive Ty : Type :=
  | TVar : var -> Ty                       (* X *)
  | TUnit : Ty                             (* Unit *)
  | TBool : Ty                             (* Bool *)
  | TInt32 : Ty                            (* Int32 *)
  | TFun : Ty -> Ty -> Ty                  (* x:A -> B_x *)
  | TForall: Ty -> Ty -> Ty -> Ty           (* forall X >: L <: U. T_X *)
  | TRefine : Ty -> Term -> Ty             (* {x:A | b} *)
  | TSigma : Ty -> Ty -> Ty                (* Sigma x:A. B_x *)
  | TSum : Ty -> Ty -> Ty                  (* A + B *)
  | TOr : Ty -> Ty -> Ty                   (* A \/ B *)
  | TAnd : Ty -> Ty -> Ty                  (* A /\ B *)
  | TTop : Ty                              (* Top *)
  | TBot : Ty                              (* Bot *)
  | TMuAll : Ty -> Ty                      (* forall k. [mu X. T_X]_k — binds 1 type var *)

(** Terms *)
with Term : Type :=
  | tunit : Term                                   (* unit *)
  | tbool : bool -> Term                           (* true | false *)
  | tint32 : Z -> Term                             (* integer literal *)
  | tvar : var -> Term                             (* x *)
  | tabs : Ty -> Term -> Term                      (* \x:A.b_x *)
  | tapp : Term -> Term -> Term                    (* f(a) *)
  | ttabs : Ty -> Ty -> Term -> Term                (* /\(X >: L <: U).b *)
  | ttapp : Term -> Ty -> Term                     (* f[A] *)
  | tlet : Ty -> Term -> Term -> Term              (* let x:A = a in b *)
  | tpair : Term -> Term -> Term                   (* (e1, e2) *)
  | tmatch_pair : Term -> Term -> Term             (* match e with (x,y) => body *)
  | tinl : Ty -> Term -> Term                       (* inl[B](e) : A + B *)
  | tinr : Ty -> Term -> Term                       (* inr[A](e) : A + B *)
  | tmatch_sum : Term -> Term -> Term -> Term      (* match e with inl(x) => l | inr(y) => r *)
  | tbin_op : BinOp -> Term -> Term -> Term        (* a op b *)
  | tif : Term -> Term -> Term -> Term             (* if a then b1 else b2 *)
  | tdiverge : Term                                (* diverging term *)
  | tloop : Term -> Term -> Term.                  (* loop a body — body binds 1 term var *)

(** ** Values

    Values are the results of evaluation, distinct from terms: while term
    lambdas may have free variables, closures capture their environment as a
    list of values. *)

(** Register the [list] induction schemes, so that [Value] (which nests
    [list] in its closure constructors) gets a nested induction principle
    instead of a [register-all] warning. *)
Scheme All for list.

Inductive Value : Type :=
  | vunit : Value
  | vbool : bool -> Value
  | vint32 : Z -> Value
  | vpair : Value -> Value -> Value        (* pair value *)
  | vinl  : Value -> Value                 (* left injection *)
  | vinr  : Value -> Value                 (* right injection *)
  | vabs  : list Value -> Term -> Value    (* term abstraction closure *)
  | vtabs : list Value -> Term -> Value.  (* type abstraction closure *)

(** ** Custom induction principle for values

    Because [Value] contains nested lists, we need a custom induction
    principle that properly handles the list structure. *)
Section Value_ind_nested.
  Variable P : Value -> Prop.
  Hypothesis Hunit : P vunit.
  Hypothesis Hbool : forall b, P (vbool b).
  Hypothesis Hint32 : forall z, P (vint32 z).
  Hypothesis Hpair : forall v1 v2, P v1 -> P v2 -> P (vpair v1 v2).
  Hypothesis Hinl : forall v, P v -> P (vinl v).
  Hypothesis Hinr : forall v, P v -> P (vinr v).
  Hypothesis Habs : forall venv body, Forall P venv -> P (vabs venv body).
  Hypothesis Htabs : forall venv body, Forall P venv -> P (vtabs venv body).

  Fixpoint Value_ind_nested (v : Value) : P v :=
    let fix env_ind (l : list Value) : Forall P l :=
      match l with
      | [] => Forall_nil P
      | v :: vs => Forall_cons v (Value_ind_nested v) (env_ind vs)
      end
    in
    match v with
    | vunit => Hunit
    | vbool b => Hbool b
    | vint32 z => Hint32 z
    | vpair v1 v2 => Hpair v1 v2 (Value_ind_nested v1) (Value_ind_nested v2)
    | vinl v => Hinl v (Value_ind_nested v)
    | vinr v => Hinr v (Value_ind_nested v)
    | vabs venv body => Habs venv body (env_ind venv)
    | vtabs venv body => Htabs venv body (env_ind venv)
    end.
End Value_ind_nested.

(** ** Decidable equality for types and terms *)
Fixpoint ty_eq_dec (x y: Ty) : {x = y} + {x <> y}
with term_eq_dec (x y: Term) : {x = y} + {x <> y}.
Proof.
  all: decide equality; auto using Nat.eq_dec, Z.eq_dec, ty_eq_dec, Bool.bool_dec, bin_op_eq_dec.
Defined.
