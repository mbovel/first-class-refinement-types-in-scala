(** Example: collect (filter into a refined list) using a loop. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import ZArith.BinInt.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.

(** * Type abbreviations *)

(** List[X] = mu self. Unit + (X, self) *)
Definition ListTy (tv : nat) : Ty :=
  TMuAll (TSum TUnit (TSigma (TVar (S tv)) (TVar 0))).

(** {v : T | p(v)} where T is at type var [tv] and p is at term var [pv].
    Inside TRefine, the refined value is tvar 0, so p shifts to tvar (S pv). *)
Definition RefinedByP (tv pv : nat) : Ty :=
  TRefine (TVar tv) (tapp (tvar (S pv)) (tvar 0)).

(** List[{v: TVar tv | p(v)}] where p = tvar pv.
    Inside TMuAll, type vars shift by 1, so tv becomes S tv. *)
Definition ListTy_refined (tv pv : nat) : Ty :=
  TMuAll (TSum TUnit (TSigma (RefinedByP (S tv) pv) (TVar 0))).

(** * Type of collect

    collect = [T] => [S >: T] =>
      (xs: List[T]) => (p: S => Bool) => (acc: List[{v: T | p(v)}]) =>
        List[{v: T | p(v)}]

    After both foralls: T = TVar 1, S = TVar 0.

    (xs: List[T]) -> ...
      Inside this TFun body, xs = tvar 0.

    (p: S => Bool) -> ...
      Inside: p = tvar 0, xs = tvar 1.

    (acc: List[{v: T | p(v)}]) -> ...
      Inside: acc = tvar 0, p = tvar 1, xs = tvar 2.
      The refinement {v: T | p(v)}: p is at tvar 1 in the outer scope,
      but inside TRefine the predicate binds v at tvar 0, so p shifts
      to tvar 2. The predicate is: tapp (tvar 2) (tvar 0).

    Return type: List[{v: T | p(v)}]
      acc = tvar 0, p = tvar 1, xs = tvar 2.
      Inside TRefine: p shifts to tvar 2.
*)

Definition collect_ty : Ty :=
  TForall TBot TTop                                  (* [T >: Bot <: Top] *)
    (TForall (TVar 0) TTop                            (* [S >: T <: Top] *)
      (TFun (ListTy 1)                                (* xs: List[T] *)
        (TFun (TFun (TVar 0) TBool)                   (* p: S => Bool *)
          (TFun (ListTy_refined 1 1)                   (* acc: List[{v:T|p(v)}] *)
            (ListTy_refined 1 2))))).                  (* => List[{v:T|p(v)}] *)

(** * Term: collect

    collect = [T] => [S >: T <: Top] =>
      \(xs: List[T]). \(p: S => Bool). \(acc: List[{v:T|p(v)}]).
        loop (xs, acc)
          \state.
            match state with (remaining, current_acc) =>
              match remaining with
              | inl(_) =>                 -- empty: break with current_acc
                  inr(current_acc)
              | inr(cons) =>
                  match cons with (head, tail) =>
                    if p(head)
                    then inl((tail, inr[Unit]((head, current_acc))))
                    else inl((tail, current_acc))
                  end
              end
            end

    Environment after abstractions (before loop):
      acc = tvar 0, p = tvar 1, xs = tvar 2

    Inside the loop body (state = tvar 0, acc = tvar 1, p = tvar 2, xs = tvar 3):
      match state with (remaining, current_acc) =>
        remaining = tvar 1, current_acc = tvar 0
        (after tmatch_pair: tvar 0 = 2nd component, tvar 1 = 1st component)
        acc = tvar 3, p = tvar 4, xs = tvar 5
*)

Definition collect_tm : Term :=
  ttabs TBot TTop                                     (* [T] *)
    (ttabs (TVar 0) TTop                              (* [S >: T] *)
      (tabs (ListTy 1)                                (* \xs *)
        (tabs (TFun (TVar 0) TBool)                   (* \p *)
          (tabs (ListTy_refined 1 1)                  (* \acc *)
            (* env: acc=0, p=1, xs=2 *)
            (tloop
              (tpair (tvar 2) (tvar 0))               (* initial: (xs, acc) *)
              (* loop body: state=0, acc=1, p=2, xs=3 *)
              (tmatch_pair (tvar 0)
                (* current_acc=0, remaining=1, state=2, acc=3, p=4, xs=5 *)
                (tmatch_sum (tvar 1)
                  (* -- inl (empty): _=0, cacc=1, rem=2, st=3, acc=4, p=5, xs=6 *)
                  (tinr TUnit (tvar 1))               (* break with current_acc *)

                  (* -- inr (cons): cv=0, cacc=1, rem=2, st=3, acc=4, p=5, xs=6 *)
                  (tmatch_pair (tvar 0)
                    (* head=1, tail=0, cv=2, cacc=3, rem=4, st=5, acc=6, p=7, xs=8 *)
                    (tif (tapp (tvar 7) (tvar 1))     (* if p(head) *)
                      (* then: continue with (tail, Cons(head, current_acc)) *)
                      (tinl TUnit
                        (tpair (tvar 0)
                          (tinr TUnit (tpair (tvar 1) (tvar 3)))))
                      (* else: continue with (tail, current_acc) *)
                      (tinl TUnit
                        (tpair (tvar 0) (tvar 3))))
                  ))
              )))))).
(** * Evaluation tests *)

Fixpoint list_term (elems : list Term) : Term :=
  match elems with
  | [] => tinl TUnit tunit
  | x :: xs => tinr TUnit (tpair x (list_term xs))
  end.

Fixpoint list_value (elems : list Value) : Value :=
  match elems with
  | [] => vinl vunit
  | x :: xs => vinr (vpair x (list_value xs))
  end.

(** is_positive : Int32 => Bool *)
Definition is_positive : Term :=
  tabs TInt32 (tbin_op OpGt (tvar 0) (tint32 0%Z)).

(** Test: collect positives from [3, -1, 4, -1, 5] starting with empty acc.
    Expected result: [5, 4, 3] (reversed, since we prepend) *)
Definition test_collect : Term :=
  tapp
    (tapp
      (tapp
        (ttapp (ttapp collect_tm TInt32) TInt32)
        (list_term (map tint32 [3%Z; (-1)%Z; 4%Z; (-1)%Z; 5%Z])))
      is_positive)
    (list_term []).

Example test_collect_ok :
  eval 1000 [] test_collect =
    Some (Some (list_value (map vint32 [5%Z; 4%Z; 3%Z]))).
Proof. native_compute. reflexivity. Qed.

(** Test: collect from empty list.
    Expected: empty list *)
Definition test_collect_empty : Term :=
  tapp
    (tapp
      (tapp
        (ttapp (ttapp collect_tm TInt32) TInt32)
        (list_term []))
      is_positive)
    (list_term []).

Example test_collect_empty_ok :
  eval 1000 [] test_collect_empty =
    Some (Some (vinl vunit)).
Proof. native_compute. reflexivity. Qed.

(** Test: collect from [-1, -2] (no positives).
    Expected: empty list *)
Definition test_collect_none : Term :=
  tapp
    (tapp
      (tapp
        (ttapp (ttapp collect_tm TInt32) TInt32)
        (list_term (map tint32 [(-1)%Z; (-2)%Z])))
      is_positive)
    (list_term []).

Example test_collect_none_ok :
  eval 1000 [] test_collect_none =
    Some (Some (vinl vunit)).
Proof. native_compute. reflexivity. Qed.
