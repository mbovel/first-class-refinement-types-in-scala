(** * De Bruijn Renaming and Substitution

    Custom two-sorted de Bruijn machinery: renamings and substitutions act
    on type variables and term variables simultaneously, since types embed
    terms (refinement predicates) and terms embed types (annotations). *)

From Stdlib Require Import Arith.PeanoNat.
Require Import RefinementTypes.Syntax.

(** ** Infrastructure *)

Definition funcomp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).

Definition scons {A : Type} (a : A) (f : nat -> A) : nat -> A :=
  fun n => match n with
  | 0 => a
  | S n => f n
  end.

Notation "f >> g" := (funcomp g f) (at level 50, left associativity).
Notation "a .: f" := (scons a f) (at level 55, right associativity).

(** ** Renaming *)

Definition upren (xi : var -> var) : var -> var :=
  0 .: (xi >> S).

Fixpoint ren_ty (xi_ty : var -> var) (xi_tm : var -> var) (T : Ty) {struct T} : Ty :=
  match T with
  | TVar n => TVar (xi_ty n)
  | TUnit => TUnit
  | TBool => TBool
  | TInt32 => TInt32
  | TFun A B => TFun (ren_ty xi_ty xi_tm A) (ren_ty xi_ty (upren xi_tm) B)
  | TForall L U B => TForall (ren_ty xi_ty xi_tm L) (ren_ty xi_ty xi_tm U) (ren_ty (upren xi_ty) xi_tm B)
  | TRefine A p => TRefine (ren_ty xi_ty xi_tm A) (ren_tm xi_ty (upren xi_tm) p)
  | TSigma A B => TSigma (ren_ty xi_ty xi_tm A) (ren_ty xi_ty (upren xi_tm) B)
  | TSum A B => TSum (ren_ty xi_ty xi_tm A) (ren_ty xi_ty xi_tm B)
  | TOr A B => TOr (ren_ty xi_ty xi_tm A) (ren_ty xi_ty xi_tm B)
  | TAnd A B => TAnd (ren_ty xi_ty xi_tm A) (ren_ty xi_ty xi_tm B)
  | TTop => TTop
  | TBot => TBot
  | TMuAll B => TMuAll (ren_ty (upren xi_ty) xi_tm B)
  end
with ren_tm (xi_ty : var -> var) (xi_tm : var -> var) (t : Term) {struct t} : Term :=
  match t with
  | tunit => tunit
  | tbool b => tbool b
  | tint32 z => tint32 z
  | tvar n => tvar (xi_tm n)
  | tabs A b => tabs (ren_ty xi_ty xi_tm A) (ren_tm xi_ty (upren xi_tm) b)
  | tapp f a => tapp (ren_tm xi_ty xi_tm f) (ren_tm xi_ty xi_tm a)
  | ttabs L U b => ttabs (ren_ty xi_ty xi_tm L) (ren_ty xi_ty xi_tm U) (ren_tm (upren xi_ty) xi_tm b)
  | ttapp e A => ttapp (ren_tm xi_ty xi_tm e) (ren_ty xi_ty xi_tm A)
  | tlet A a b => tlet (ren_ty xi_ty xi_tm A) (ren_tm xi_ty xi_tm a) (ren_tm xi_ty (upren xi_tm) b)
  | tpair a b => tpair (ren_tm xi_ty xi_tm a) (ren_tm xi_ty xi_tm b)
  | tmatch_pair e b => tmatch_pair (ren_tm xi_ty xi_tm e) (ren_tm xi_ty (upren (upren xi_tm)) b)
  | tinl B e => tinl (ren_ty xi_ty xi_tm B) (ren_tm xi_ty xi_tm e)
  | tinr A e => tinr (ren_ty xi_ty xi_tm A) (ren_tm xi_ty xi_tm e)
  | tmatch_sum e l r => tmatch_sum (ren_tm xi_ty xi_tm e) (ren_tm xi_ty (upren xi_tm) l) (ren_tm xi_ty (upren xi_tm) r)
  | tbin_op op a b => tbin_op op (ren_tm xi_ty xi_tm a) (ren_tm xi_ty xi_tm b)
  | tif c t f => tif (ren_tm xi_ty xi_tm c) (ren_tm xi_ty xi_tm t) (ren_tm xi_ty xi_tm f)
  | tdiverge => tdiverge
  | tloop a body => tloop (ren_tm xi_ty xi_tm a) (ren_tm xi_ty (upren xi_tm) body)
  end.

(** ** Substitution helpers

    When crossing a binder, we must lift BOTH substitutions:
    - The substitution for the bound sort gets a new binding (scons) + shift
    - The substitution for the OTHER sort gets its range shifted (cross-sort shift)

    Naming convention: [up_X_Y] = lifting the Y-substitution when crossing an X-binder.
    Diagonal (up_ty_ty, up_tm_tm): adds new binding + shifts same-sort vars in range.
    Off-diagonal (up_ty_tm, up_tm_ty): shifts other-sort vars in range, no new binding. *)

(** Crossing a type binder: *)
Definition up_ty_ty (sigma_ty : var -> Ty) : var -> Ty :=
  TVar 0 .: (sigma_ty >> ren_ty S id).

Definition up_ty_tm (sigma_tm : var -> Term) : var -> Term :=
  sigma_tm >> ren_tm S id.

(** Crossing a term binder: *)
Definition up_tm_ty (sigma_ty : var -> Ty) : var -> Ty :=
  sigma_ty >> ren_ty id S.

Definition up_tm_tm (sigma_tm : var -> Term) : var -> Term :=
  tvar 0 .: (sigma_tm >> ren_tm id S).

(** ** Substitution *)

Fixpoint subst_ty (sigma_ty : var -> Ty) (sigma_tm : var -> Term) (T : Ty) {struct T} : Ty :=
  match T with
  | TVar n => sigma_ty n
  | TUnit => TUnit
  | TBool => TBool
  | TInt32 => TInt32
  | TFun A B => TFun (subst_ty sigma_ty sigma_tm A)
                      (subst_ty (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) B)
  | TForall L U B => TForall (subst_ty sigma_ty sigma_tm L) (subst_ty sigma_ty sigma_tm U) (subst_ty (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) B)
  | TRefine A p => TRefine (subst_ty sigma_ty sigma_tm A)
                            (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) p)
  | TSigma A B => TSigma (subst_ty sigma_ty sigma_tm A)
                          (subst_ty (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) B)
  | TSum A B => TSum (subst_ty sigma_ty sigma_tm A) (subst_ty sigma_ty sigma_tm B)
  | TOr A B => TOr (subst_ty sigma_ty sigma_tm A) (subst_ty sigma_ty sigma_tm B)
  | TAnd A B => TAnd (subst_ty sigma_ty sigma_tm A) (subst_ty sigma_ty sigma_tm B)
  | TTop => TTop
  | TBot => TBot
  | TMuAll B => TMuAll (subst_ty (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) B)
  end
with subst_tm (sigma_ty : var -> Ty) (sigma_tm : var -> Term) (t : Term) {struct t} : Term :=
  match t with
  | tunit => tunit
  | tbool b => tbool b
  | tint32 z => tint32 z
  | tvar n => sigma_tm n
  | tabs A b => tabs (subst_ty sigma_ty sigma_tm A)
                     (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) b)
  | tapp f a => tapp (subst_tm sigma_ty sigma_tm f) (subst_tm sigma_ty sigma_tm a)
  | ttabs L U b => ttabs (subst_ty sigma_ty sigma_tm L) (subst_ty sigma_ty sigma_tm U) (subst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) b)
  | ttapp e A => ttapp (subst_tm sigma_ty sigma_tm e) (subst_ty sigma_ty sigma_tm A)
  | tlet A a b => tlet (subst_ty sigma_ty sigma_tm A)
                       (subst_tm sigma_ty sigma_tm a)
                       (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) b)
  | tpair a b => tpair (subst_tm sigma_ty sigma_tm a) (subst_tm sigma_ty sigma_tm b)
  | tmatch_pair e b => tmatch_pair (subst_tm sigma_ty sigma_tm e)
                                   (subst_tm (up_tm_ty (up_tm_ty sigma_ty))
                                             (up_tm_tm (up_tm_tm sigma_tm)) b)
  | tinl B e => tinl (subst_ty sigma_ty sigma_tm B) (subst_tm sigma_ty sigma_tm e)
  | tinr A e => tinr (subst_ty sigma_ty sigma_tm A) (subst_tm sigma_ty sigma_tm e)
  | tmatch_sum e l r => tmatch_sum (subst_tm sigma_ty sigma_tm e)
                                    (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) l)
                                    (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) r)
  | tbin_op op a b => tbin_op op (subst_tm sigma_ty sigma_tm a) (subst_tm sigma_ty sigma_tm b)
  | tif c t f => tif (subst_tm sigma_ty sigma_tm c) (subst_tm sigma_ty sigma_tm t) (subst_tm sigma_ty sigma_tm f)
  | tdiverge => tdiverge
  | tloop a body => tloop (subst_tm sigma_ty sigma_tm a)
                          (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) body)
  end.

(** ** Iterated up *)

Fixpoint upn_tm (n : nat) (sigma : var -> Term) : var -> Term :=
  match n with
  | 0 => sigma
  | S n => up_tm_tm (upn_tm n sigma)
  end.

(** ** Derived operations *)

(** Substitute type var 0 with U in T. *)
Definition ty_subst (T : Ty) (U : Ty) : Ty :=
  subst_ty (U .: TVar) tvar T.

(** Abstract term variable [i] out of a type: maps variable [i] to variable 0
    and shifts all other variables up. This is the inverse of [tvar i .: tvar]. *)
Definition abstract_term_var (i : nat) : var -> Term :=
  fun j => if Nat.eq_dec j i then tvar 0 else tvar (S j).
