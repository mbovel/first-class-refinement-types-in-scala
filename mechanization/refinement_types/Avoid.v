(** * Avoidance

    This file defines the avoidance function that removes references to a
    specific term variable from a type. This is used for typing let bindings
    where the result type may reference the bound variable.

    The key insight is that refinement predicates can be approximated:
    - In positive position: replace the predicate with [true] (weaker)
    - In negative position: replace the predicate with [false] (stronger)

    This maintains the subtyping relationship:
    - Positive: original <: avoided (avoided is a supertype)
    - Negative: avoided <: original (avoided is a subtype)
*)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Positivity.

(** Polarity for tracking positive/negative positions in types *)
Inductive Polarity := Pos | Neg.

Definition flip_polarity (p: Polarity) : Polarity :=
  match p with
  | Pos => Neg
  | Neg => Pos
  end.

(** Check if a term variable [i] occurs free in a term [t] *)
Fixpoint term_mentions (i: nat) (t: Term) : bool :=
  match t with
  | tunit => false
  | tbool _ => false
  | tint32 _ => false
  | tvar j => Nat.eqb i j
  | tabs A b => term_mentions_ty i A || term_mentions (S i) b
  | tapp f a => term_mentions i f || term_mentions i a
  | ttabs L U b => term_mentions_ty i L || term_mentions_ty i U || term_mentions i b
  | ttapp f A => term_mentions i f || term_mentions_ty i A
  | tlet A e b => term_mentions_ty i A || term_mentions i e || term_mentions (S i) b
  | tpair e1 e2 => term_mentions i e1 || term_mentions i e2
  | tmatch_pair e body => term_mentions i e || term_mentions (S (S i)) body
  | tinl B e => term_mentions_ty i B || term_mentions i e
  | tinr A e => term_mentions_ty i A || term_mentions i e
  | tmatch_sum e l r => term_mentions i e || term_mentions (S i) l || term_mentions (S i) r
  | tbin_op _ a b => term_mentions i a || term_mentions i b
  | tif c t e => term_mentions i c || term_mentions i t || term_mentions i e
  | tdiverge => false
  | tloop a body => term_mentions i a || term_mentions (S i) body
  end
with term_mentions_ty (i: nat) (T: Ty) : bool :=
  match T with
  | TVar _ => false
  | TUnit => false
  | TBool => false
  | TInt32 => false
  | TFun A B => term_mentions_ty i A || term_mentions_ty (S i) B
  | TForall L U B => term_mentions_ty i L || term_mentions_ty i U || term_mentions_ty i B
  | TRefine A p => term_mentions_ty i A || term_mentions (S i) p
  | TSigma A B => term_mentions_ty i A || term_mentions_ty (S i) B
  | TSum A B => term_mentions_ty i A || term_mentions_ty i B
  | TOr A B => term_mentions_ty i A || term_mentions_ty i B
  | TAnd A B => term_mentions_ty i A || term_mentions_ty i B
  | TTop => false
  | TBot => false
  | TMuAll B => term_mentions_ty i B
  end.

(** Avoidance: remove references to variable [i] from type [T].

    When a refinement predicate mentions variable [i], we replace it with
    [true] or [false] depending on polarity:
    - Positive polarity: use [true] (weakens the type, making it a supertype)
    - Negative polarity: use [false] (strengthens the type, making it a subtype)

    The [depth] parameter tracks how many term binders we've gone under,
    so we can correctly identify references to variable [i].
*)
Fixpoint avoid (pol: Polarity) (i: nat) (T: Ty) : Ty :=
  match T with
  | TVar X => TVar X
  | TUnit => TUnit
  | TBool => TBool
  | TInt32 => TInt32
  | TFun A B =>
      TFun (avoid (flip_polarity pol) i A) (avoid pol (S i) B)
  | TForall L U B =>
      TForall (avoid pol i L) (avoid (flip_polarity pol) i U) (avoid pol i B)
  | TRefine A p =>
      let A' := avoid pol i A in
      if term_mentions (S i) p then
        match pol with
        | Pos => TRefine A' (tbool true)
        | Neg => TRefine A' (tbool false)
        end
      else
        TRefine A' p
  | TSigma A B =>
      TSigma (avoid pol i A) (avoid pol (S i) B)
  | TSum A B =>
      TSum (avoid pol i A) (avoid pol i B)
  | TOr A B =>
      TOr (avoid pol i A) (avoid pol i B)
  | TAnd A B =>
      TAnd (avoid pol i A) (avoid pol i B)
  | TTop => TTop
  | TBot => TBot
  | TMuAll B =>
      if spos 0 B then TMuAll (avoid pol i B)
      else match pol with Pos => TTop | Neg => TBot end
  end.

(** Convenience function: avoid variable 0 in positive polarity.
    This is the common case for let bindings where the body type
    may reference the bound variable.
    Note: the result is in the same environment as the input. *)
Definition avoid_var0 := avoid Pos 0.
