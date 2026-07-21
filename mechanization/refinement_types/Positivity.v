(** * Strict Positivity (Figure 11)

    Defines a predicate [spos i T] that checks whether type variable [i]
    appears only in strictly positive positions in type [T]: never to the
    left of a function arrow, and never in the bounds of a universal type.

    Also defines [ty_var_absent i T] that checks whether type variable [i]
    does not appear at all in [T].

    Note on TRefine: type variables inside the predicate term [p] don't
    affect [interp] through [tvars] because [interp_refine] evaluates [p]
    directly without consulting [tvars]. So we only check the base type. *)

Require Import RefinementTypes.Syntax.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.

(** [ty_var_absent i T] checks that type variable [i] does not occur
    free in [T]. *)
Fixpoint ty_var_absent (i: nat) (T: Ty) : bool :=
  match T with
  | TVar j => negb (Nat.eqb i j)
  | TUnit | TBool | TInt32 | TTop | TBot => true
  | TFun A B | TOr A B | TAnd A B | TSigma A B | TSum A B =>
      ty_var_absent i A && ty_var_absent i B
  | TForall L U B =>
      ty_var_absent i L && ty_var_absent i U && ty_var_absent (S i) B
  | TMuAll B => ty_var_absent (S i) B
  | TRefine A _ => ty_var_absent i A
  end.

(** [spos i T] checks that type variable [i] appears only in strictly
    positive positions in [T].

    - In function types [TFun A B], variable [i] must be absent from [A]
      (the negative position) and strictly positive in [B].
    - In union types [TOr A B], variable [i] must be absent from both
      branches (the distributing lemma fails for TOr in general).
    - Under type binders [TForall L U B], [TMuAll B], the index shifts.
    - For [TMuAll B], we require that the recursive variable (position 0)
      is strictly positive in [B], AND that the tracked variable [i]
      (shifted to [S i]) is completely absent from [B]. The absence
      condition is needed for the distributing lemma: when collecting
      a universal quantifier through a recursive type, the recursive
      approximations at position 0 depend on the outer variable, creating
      a circularity that can only be broken if the outer variable is
      absent. This follows Hamza et al. 2019 (System FR), where
      [T_rec] requires [no_type_fvar] for the tracked variables. *)
Fixpoint spos (i: nat) (T: Ty) : bool :=
  match T with
  | TVar _ | TUnit | TBool | TInt32 | TTop | TBot => true
  | TFun A B => ty_var_absent i A && spos i B
  | TForall L U B => ty_var_absent i L && ty_var_absent i U && spos (S i) B
  | TMuAll B => spos 0 B && ty_var_absent (S i) B
  | TRefine A _ => spos i A
  | TOr A B => ty_var_absent i A && ty_var_absent i B
  | TSum A B => spos i A && spos i B
  | TAnd A B | TSigma A B => spos i A && spos i B
  end.
