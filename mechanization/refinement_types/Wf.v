(** * Well-Formed Environments (Figure 8)

    Typing contexts Γ and the well-formedness predicate wf(δ, Γ, ρ) of the
    paper, defined from its three components: [wf_env] for term bindings,
    [wf_benv] for type variable bounds, and [wf_facts] for equality
    facts. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Interp.

(** ** Term bindings *)

(** Well-formed environment: each type T_i is interpreted with the suffix
    venv[i+1:], so that T_i only sees bindings that were introduced before it.
    Types in tenv use relative de Bruijn indices (variable 0 refers to the
    next binding in the suffix, not to position 0 in the full environment). *)
Fixpoint wf_env (tvars: list SemTy) (tenv: list Ty) (venv: list Value) : Prop :=
  match tenv, venv with
  | [], [] => True
  | T :: tenv', v :: venv' =>
      interp tvars venv' T v /\ wf_env tvars tenv' venv'
  | _, _ => False
  end.

(** ** Equality facts *)

(** Two terms evaluate to the same value in (possibly different) environments. *)
Definition evals_to_same (venv1: list Value) (t1: Term)
                         (venv2: list Value) (t2: Term) : Prop :=
  exists v fuel1 fuel2,
    eval fuel1 venv1 t1 = Some (Some v) /\
    eval fuel2 venv2 t2 = Some (Some v).

(** Well-formed facts: each fact is a pair of depth-tagged terms that evaluate
    to the same value. Each side has its own depth d_i indicating how many
    bindings were in scope; the term is evaluated in the corresponding suffix
    of venv. *)
Definition wf_facts (venv: list Value) (facts: list ((nat * Term) * (nat * Term))) : Prop :=
  Forall (fun '((d1, t1), (d2, t2)) =>
    d1 <= length venv /\ d2 <= length venv /\
    evals_to_same (skipn (length venv - d1) venv) t1
                  (skipn (length venv - d2) venv) t2) facts.

(** ** Type variable bounds *)

(** A bounds environment maps each type variable to a lower and upper bound.
    Bounds at position [i] are in the scope where type variables [0..i-1]
    do not exist yet, so they are interpreted with [skipn (S i) tvars]. *)
Definition TBounds := list (Ty * Ty).

(** Well-formedness of the bounds environment: each type variable [A_i]
    satisfies [L_i <: A_i <: U_i], where bounds are interpreted using
    [tvars'] (the tail), matching their introduction scope. *)
Fixpoint wf_benv (tvars: list SemTy) (tbounds: TBounds) (venv: list Value) : Prop :=
  match tvars, tbounds with
  | [], [] => True
  | A :: tvars', (L, U) :: tbounds' =>
      (forall w, interp tvars' venv L w -> A w) /\
      (forall w, A w -> interp tvars' venv U w) /\
      wf_benv tvars' tbounds' venv
  | _, _ => False
  end.

(** Shift bounds to account for a new term variable in scope. *)
Definition tbounds_shift_term (tb: TBounds) : TBounds :=
  map (fun '(L, U) => (ren_ty id S L, ren_ty id S U)) tb.

(** ** Typing contexts Γ

    A context has three kinds of entries (Figure 5): term bindings
    [x : A], type variable bounds [X :> L <: U] and equality facts
    [a1 ~ a2]. The mechanization keeps the three kinds in separate lists,
    each indexed by its own de Bruijn indices. Types stored in the context
    are kept relative to the current scope: pushing a term binding shifts
    the bounds, and pushing a type variable shifts the term bindings. *)

Definition Fact : Type := ((nat * Term) * (nat * Term))%type.

Record Ctx := mkCtx {
  ctx_tenv : list Ty;
  ctx_tbounds : TBounds;
  ctx_facts : list Fact
}.

Definition ctx_empty : Ctx :=
  {| ctx_tenv := []; ctx_tbounds := []; ctx_facts := [] |}.

(** Number of term bindings in scope; the depth tag of facts. *)
Definition ctx_len (G : Ctx) : nat := length (ctx_tenv G).

Definition tenv_shift_type (types : list Ty) : list Ty :=
  List.map (ren_ty S id) types.

(** Γ, x : A *)
Definition ctx_cons_term (G : Ctx) (A : Ty) : Ctx :=
  {| ctx_tenv := A :: ctx_tenv G;
     ctx_tbounds := tbounds_shift_term (ctx_tbounds G);
     ctx_facts := ctx_facts G |}.

(** Γ, X :> L <: U *)
Definition ctx_cons_type (G : Ctx) (L U : Ty) : Ctx :=
  {| ctx_tenv := tenv_shift_type (ctx_tenv G);
     ctx_tbounds := (L, U) :: ctx_tbounds G;
     ctx_facts := ctx_facts G |}.

(** Γ, a1 ~ a2 *)
Definition ctx_add_fact (G : Ctx) (f : Fact) : Ctx :=
  {| ctx_tenv := ctx_tenv G;
     ctx_tbounds := ctx_tbounds G;
     ctx_facts := f :: ctx_facts G |}.

(** ** Context well-formedness wf(δ, Γ, ρ) (Figure 8) *)

Definition wf_ctx (tvars : list SemTy) (G : Ctx) (venv : list Value) : Prop :=
  wf_env tvars (ctx_tenv G) venv /\
  wf_benv tvars (ctx_tbounds G) venv /\
  wf_facts venv (ctx_facts G).
