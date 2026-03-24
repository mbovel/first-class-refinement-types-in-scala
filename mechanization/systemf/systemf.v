From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
Require Import Autosubst.Autosubst.

Global Hint Extern 1000 => lia : lia.


(*
Soundness proof of System-F with erased terms, using:
- A definitional interpreter
- Autosubst
- Semantic types

See:
- Type Soundness Proofs with Definitional Interpreters
  Nada Amin and Tiark Rompf
  POPL 2017
  https://doi.org/10.1145/3093333.3009866
  https://github.com/TiarkRompf/minidot/tree/master/popl17
- Autosubst: Reasoning with de Bruijn Terms and Parallel Substitutions
  Steven Schäfer, Tobias Tebbi and Gert Smolka
  ITP 2015
  https://doi.org/10.1007/978-3-319-22102-1_24
  https://www.ps.uni-saarland.de/autosubst/
- A Logical Approach to Type Soundness
  Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal
  Journal of the ACM, 2024
  https://doi.org/10.1145/3676954
  https://gitlab.mpi-sws.org/iris/examples/-/tree/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc
*)


(*** Definitions ***)
(* Inspired by https://github.com/TiarkRompf/minidot/blob/master/popl17/fsub.v#L19-L48 *)

(* Types *)
Inductive Ty : Type :=
  | TVar : var -> Ty (* X *)
  | TBool : Ty (* Bool *)
  | TFun : Ty -> Ty -> Ty (* A -> B *)
  | TForall : {bind Ty} -> Ty (* forall X. T *)
.
(* Note: `var` and `bind` are defined in Autosubst. `var` is just `nat` and
`{bind Ty}` is `Ty` with one de Bruijn index binding. *)

(* Decidable equality on types *)
Definition ty_eq_dec: forall x y: Ty, {x = y} + {x <> y}.
Proof. decide equality; auto using Nat.eq_dec. Defined.

(* Type environments *)
Definition TyEnv := list Ty.

(* Terms *)
Inductive Term : Type :=
  | tbool : bool -> Term (* true | false *)
  | tvar : nat -> Term (* x *)
  | tabs : Ty -> Term -> Term (* \_:A.b *)
  | tapp : Term -> Term -> Term (* f(a) *)
  | ttabs : Term -> Term (* /\.b *)
  | ttapp : Term -> Ty -> Term (* f[A] *)
.
(* Note: `tvar` also uses de Bruijn indices, but not managed by Autosubst. *)

(* Values *)
Inductive Value : Type :=
  | vbool : bool -> Value
  | vabs  : (list Value) -> Term -> Value
  | vtabs : (list Value) -> Term -> Value
.
(* Note: `vabs` closures capture the environment at definition site. *)
(* Note: `vtabs` are type closures and also capture the value environment. They
don't need type environments because types are erased. *)

(* Value environments *)
Definition ValueEnv := list Value.

(* Semantic types *)
(* A semantic type is a predicate on values. *)
Definition SemTy : Type := Value -> Prop.


(*** Autosubst instances for types and type substitution examples ***)
(* See https://www.ps.uni-saarland.de/autosubst/ *)

Global Instance Ids_Ty : Ids Ty. derive. Defined.
Global Instance Rename_Ty : Rename Ty. derive. Defined.
Global Instance Subst_Ty : Subst Ty. derive. Defined.
Global Instance SubstLemmas_Ty : SubstLemmas Ty. derive. Defined.

Example ty_subst_ex_1: forall A,
  (TVar 0).[A/] = A.
Proof. reflexivity. Qed.

Example ty_subst_ex_2: forall A,
  (TForall (TVar 0)).[A/] = TForall (TVar 0).
Proof. reflexivity. Qed.

Example ty_subst_ex_3: forall A,
  (TForall (TVar 1)).[A/] = TForall (A.[ren(+1)]).
Proof. simpl. intros. autosubst. Qed.

Example ty_subst_ex_4: forall A,
  (TForall (TVar 2)).[A/] = TForall (TVar 1).
Proof. reflexivity. Qed.


(*** Definitional interpreter ***)
(* Similar to https://github.com/TiarkRompf/minidot/blob/master/popl17/fsub.v#L302-L344 *)
(*
The result is a layered option type:
- None             means timeout
- Some None        means stuck
- Some (Some v))   means result v
The layered approach simplifies proofs, compared to using a single sum type.
*)
Fixpoint eval (fuel: nat) (env: ValueEnv) (t: Term) : option (option Value) :=
  match fuel with
  | 0 => None
  | S fuel =>
    match t with
    | tbool b => Some (Some (vbool b))
    | tvar i =>
        match (nth_error env i) with
        | None => Some (None)
        | Some v => Some (Some v)
        end
    | tabs A b => Some (Some (vabs env b))
    | ttabs b => Some (Some (vtabs env b))
    | tapp f a =>
        match (eval fuel env f) with
        | None => None
        | Some (Some (vabs envf b)) =>
            match (eval fuel env a) with
            | None => None
            | Some None => Some None
            | Some (Some va) => eval fuel (va::envf) b
            end
        | _ => Some None
        end
    | ttapp f A =>
        match (eval fuel env f) with
        | None => None
        | Some (Some (vtabs envf b)) =>
            eval fuel envf b
        | _ => Some None
        end
    end
  end.


(*** Tactics ***)

Ltac injects :=
  repeat match goal with
  | [ H: _ = _ |- _ ] => injection H; clear H; intros; subst
  end.

Ltac destruct_single x :=
  destruct x eqn:?; try discriminate; try lia; injects; eauto; let n:= numgoals in guard n < 2.

Ltac destruct_match :=
  match goal with
  | H : context [match ?x with _ => _ end] |- _ => destruct_single x
  | |- context [match ?x with _ => _ end] => destruct_single x
  end.

(*** List lemmas ***)
(* Could add these to the Coq standard library? *)

Lemma Forall2_exists2: forall {A B: Type} (R: A -> B -> Prop) (l1: list A) (l2: list B) (i: nat) (a: A),
  Forall2 R l1 l2 ->
  nth_error l1 i = Some a ->
  exists b, nth_error l2 i = Some b /\ R a b.
Proof.
  intros.
  generalize dependent i.
  induction H; intros.
  - rewrite nth_error_nil in H0. discriminate.
  - destruct i; injects.
    + exists y. auto.
    + eauto using IHForall2.
Qed.

Lemma Forall2_implies: forall {A B: Type} (R1 R2: A -> B -> Prop) l1 l2,
  (forall a b, R1 a b -> R2 a b) ->
  Forall2 R1 l1 l2 ->
  Forall2 R2 l1 l2.
Proof.
  intros.
  induction H0; constructor; auto.
Qed.


(*** Evaluation lemmas ***)

(* Evaluation is monotonic in fuel: if a term evaluates with some fuel, it will
also evaluate with more fuel, to the same result (including if it's an error) *)
Lemma eval_mono: forall fuel1 fuel2 env t r,
  fuel1 <= fuel2 ->
  eval fuel1 env t = Some r ->
  eval fuel2 env t = Some r.
Proof.
  induction fuel1; intros; try discriminate.
  destruct fuel2; try lia.
  assert (fuel1 <= fuel2) by lia.
  destruct t; auto; simpl in *; repeat (repeat destruct_match; erewrite IHfuel1; eauto).
Qed.


(*** Types interpretation ***)
(* Conceptually similar to https://gitlab.mpi-sws.org/iris/examples/-/blob/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc/unary/logrel.v#L22-104 and https://github.com/epfl-lara/SystemFR/blob/master/ReducibilityDefinition.v#L29 *)

(* A term has a semantic type if it can evaluate (given enough fuel) to a value
that satisfies the semantic type. *)
Definition term_has_semtype (env: ValueEnv) (t: Term) (denot: SemTy) : Prop :=
  exists v fuel, (eval fuel env t) = Some (Some v) /\ denot v.

Definition interp_var (tenv: list SemTy) (i: nat) (v: Value) : Prop :=
  match (nth_error tenv i) with
  | Some A => A v
  | None => False (* Proof-irrelevant *)
  end.

Definition interp_bool (v: Value) : Prop :=
  exists b, v = vbool b.

Definition interp_fun (A: SemTy) (B: SemTy) (v: Value) : Prop :=
  exists env body,
    v = vabs env body /\
    forall arg, A arg -> term_has_semtype (arg::env) body B.

Definition interp_forall (F: SemTy -> SemTy) (v: Value) : Prop :=
  exists env body,
    v = vtabs env body /\
    forall A, term_has_semtype env body (F A).

(* Value interpreation, a.k.a type denotation *)
Fixpoint interp (tenv: list SemTy) (T: Ty) : SemTy :=
  match T with
  | TVar i => interp_var tenv i
  | TBool => interp_bool
  | TFun A B => interp_fun (interp tenv A) (interp tenv B)
  | TForall B => interp_forall (fun A => interp (A::tenv) B)
  end.


(*** Autosubst lemmas ***)

(* Same as https://gitlab.mpi-sws.org/iris/examples/-/blob/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc/base.v#L13-18 *)
Lemma iter_up: forall (m x : nat) (f : var -> Ty),
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
Proof.
  induction m as [|m IH]; intros; asimpl in *.
  - auto using Nat.sub_0_r.
  - unfold upn, up.
    destruct x; try reflexivity.
    simpl.
    erewrite IH.
    destruct (lt_dec x m), (lt_dec (S x) (S m)); simpl; try lia; autosubst.
Qed.

Lemma upn_rename: forall n T,
  rename (+n) T = T.[upn 0 (ren (+n))].
Proof.
  intros.
  autosubst.
Qed.


(*** Interpretation lemmas ***)

(* Similar to https://gitlab.mpi-sws.org/iris/examples/-/blob/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc/unary/logrel.v#L119-136 *)
Lemma interp_weaken: forall T tenv1 tenv2 tenv3,
  interp (tenv1 ++ tenv3) T =
  interp (tenv1 ++ tenv2 ++ tenv3) T.[upn (length tenv1) (ren (+ length tenv2))].
Proof.
  induction T as [n| |A IHA B IHB|B IHB]; intros tenv1 tenv2 tenv3; simpl; try reflexivity.
  - (* TVar *)
    rewrite iter_up.
    destruct (lt_dec _ _); simpl; unfold interp_var.
    + repeat rewrite nth_error_app1; auto.
    + repeat rewrite nth_error_app2; try lia.
      replace ((length tenv1 + (length tenv2 + (n - length tenv1)) - length tenv1 - length tenv2)) with (n - length tenv1) by lia.
      reflexivity.
  - (* TFun *)
    f_equal; eauto using functional_extensionality.
  - (* TForall *)
    f_equal.
    apply functional_extensionality.
    intros U'.
    apply IHB with (tenv1:=U'::tenv1).
Qed.

(* Similar to https://gitlab.mpi-sws.org/iris/examples/-/blob/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc/unary/logrel.v#L187-193 *)
Lemma interp_env_ren: forall T tenv T',
  interp tenv T = interp (T'::tenv) T.[ren(+1)].
Proof.
  intros.
  apply interp_weaken with (tenv1:=[]) (tenv2:=[T']) (tenv3:=tenv).
Qed.

(* Similar to https://gitlab.mpi-sws.org/iris/examples/-/blob/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc/unary/logrel.v#L138-159 *)
Lemma interp_subst_up: forall T U tenv1 tenv2,
  interp (tenv1 ++ (interp tenv2 U) :: tenv2) T =
  interp (tenv1 ++ tenv2) T.[upn (length tenv1) (U .: ids)].
Proof.
  induction T as [n| |A IHA B IHB|B IHB]; intros; simpl; try reflexivity.
  - (* TVar *)
    rewrite iter_up.
    destruct (lt_dec n (length tenv1)); simpl; unfold interp_var.
    + (* n < length tenv1 *)
      repeat rewrite nth_error_app1; auto.
    + (* n >= length tenv1 *)
      rewrite nth_error_app2; try lia.
      destruct (Nat.eq_dec n (length tenv1)); subst.
      * (* n = length tenv1 *)
        rewrite Nat.sub_diag.
        simpl.
        rewrite interp_weaken with (tenv1:=[]) (tenv2:=tenv1) (tenv3:=tenv2).
        rewrite upn_rename.
        reflexivity.
      * (* n <> length tenv1 *)
        destruct n; try lia.
        replace (S n - length tenv1) with (S (n - length tenv1)) by lia.
        simpl.
        unfold interp_var.
        rewrite <- nth_error_app2; try lia.
        replace (length tenv1 + (n - length tenv1)) with (n) by lia.
        reflexivity.
  - f_equal; eauto using functional_extensionality.
  - f_equal; eauto using functional_extensionality.
    apply functional_extensionality.
    intros U'.
    apply IHB with (tenv1:=U'::tenv1).
Qed.
    
(* Similar to https://gitlab.mpi-sws.org/iris/examples/-/blob/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc/unary/logrel.v#L161-162 *)
Lemma interp_subst: forall B tenv' A,
  interp (interp tenv' A :: tenv') B =
  interp tenv' B.[A/].
Proof.
  intros.
  apply interp_subst_up with (tenv1:=[]) (tenv2:=tenv').
Qed.


(*** Semantic typing ***)
(* Similar to https://gitlab.mpi-sws.org/iris/examples/-/blob/c3ff995b656b541847738814bc9aa107fccae622/theories/logrel/F_mu_ref_conc/unary/fundamental.v *)
(* With semantic types, we _prove_ typing rules instead of assuming them. *)

Definition wf_env (tenv: TyEnv) (env: ValueEnv) (tenv': list SemTy) : Prop :=
  Forall2 (interp tenv') tenv env.

Definition sem_typed (tenv: TyEnv) (t: Term) (T: Ty) : Prop :=
  forall env tenv',
    wf_env tenv env tenv' ->
    term_has_semtype env t (interp tenv' T).

Lemma sem_typed_bool: forall tenv b,
  sem_typed tenv (tbool b) TBool.
Proof.
  intros ** env tenv' Henv.
  exists (vbool b), 1. simpl.
  split; try reflexivity.
  exists b. reflexivity.
Qed.

Lemma sem_typed_var: forall tenv i T,
  nth_error tenv i = Some T ->
  sem_typed tenv (tvar i) T.
Proof.
  intros ** env tenv' Henv.
  eapply Forall2_exists2 in H; eauto.
  destruct H as [v [Hnth Hty]].
  exists v, 1. simpl.
  split; try assumption.
  rewrite Hnth.
  reflexivity.
Qed.

Lemma sem_typed_abs: forall tenv A b B,
  sem_typed (A::tenv) b B ->
  sem_typed tenv (tabs A b) (TFun A B).
Proof.
  intros ** env tenv' Henv.
  exists (vabs env b), 1. simpl.
  split; try reflexivity.
  exists env, b. split; auto.
  intros arg Harg.
  eapply H.
  constructor; auto.
Qed.

Lemma sem_typed_app: forall tenv f a A B,
  sem_typed tenv f (TFun A B) ->
  sem_typed tenv a A ->
  sem_typed tenv (tapp f a) B.
Proof.
  intros ** env tenv' Henv.
  destruct (H env tenv' Henv) as [vf [fuelf [Hevalf Hf]]].
  destruct (H0 env tenv' Henv) as [va [fuela [Hevala Ha]]].
  destruct Hf as [envf [body [Hvf Hf]]].
  destruct (Hf va Ha) as [v [fuelt [Hevalt Hty]]].
  exists v, (S (fuelf + fuela + fuelt)); simpl.
  rewrite eval_mono with (fuel1 := fuelf) (r := Some vf); try lia; auto.
  rewrite eval_mono with (fuel1 := fuela) (r := Some va); try lia; auto.
  rewrite Hvf.
  rewrite eval_mono with (fuel1 := fuelt) (r := Some v); try lia; auto.
Qed.

Definition tenv_incr (types: TyEnv): TyEnv :=
  List.map (fun T => T.[ren (+1)]) types.

Lemma env_incr_wf: forall tenv env tenv' T',
  wf_env tenv env tenv' ->
  wf_env (tenv_incr tenv) env (T' :: tenv').
Proof.
  intros.
  induction H; constructor; auto.
  erewrite <- interp_env_ren; auto.
Qed.

Lemma sem_typed_tabs: forall tenv b A,
  sem_typed (tenv_incr tenv) b A ->
  sem_typed tenv (ttabs b) (TForall A).
Proof.
  intros ** env tenv' Henv.
  exists (vtabs env b), 1; simpl; split; auto.
  exists env, b; split; auto.
  auto using H, env_incr_wf.
Qed.

Lemma sem_typed_tapp: forall tenv f A B,
  sem_typed tenv f (TForall B) ->
  sem_typed tenv (ttapp f A) (B.[A/]).
Proof.
  intros ** env tenv' Henv.
  destruct (H env tenv' Henv) as [vf [fuelf [Hevalf Hf]]].
  destruct Hf as [envf [body [Hvf Hf]]].
  destruct (Hf (interp tenv' A)) as [v [fuelt [Hevalt Hty]]].
  exists v, (S (fuelf + fuelt)); simpl.
  rewrite eval_mono with (fuel1 := fuelf) (r := Some vf); try lia; auto.
  rewrite Hvf.
  rewrite eval_mono with (fuel1 := fuelt) (r := Some v); try lia; auto.
  split; try reflexivity.
  rewrite <- interp_subst; auto.
Qed.


(*** Algorithmic typing ***)
Fixpoint typeof (tenv: TyEnv) (t: Term) : option Ty :=
  match t with
  | tbool _ => Some TBool
  | tvar i =>
      match (nth_error tenv i) with
      | Some T => Some T
      | None => None
      end
  | tabs A b =>
      match (typeof (A::tenv) b) with
      | Some B => Some (TFun A B)
      | _ => None
      end
  | tapp f a =>
      match (typeof tenv f) with
      | Some (TFun A B) =>
          match (typeof tenv a) with
          | Some A' => if (ty_eq_dec A A') then Some B else None
          | _ => None
          end
      | _ => None
      end
  | ttabs b =>
      match (typeof (tenv_incr tenv) b) with
      | Some B => Some (TForall B)
      | _ => None
      end
  | ttapp f A =>
      match (typeof tenv f) with
      | Some (TForall B) => Some (B.[A/])
      | _ => None
      end
  end.


(*** Full safety theorem: if a term is algorithmically typed, it is also
semantically typed; meaning evaluating it will not get stuck nor return an
error, and the returned value will be in the interpretation of its syntactic
type. ***)
Theorem full_safety: forall t T tenv,
  typeof tenv t = Some T -> sem_typed tenv t T.
Proof.
  induction t; intros; simpl in *; injects; repeat destruct_match; subst.
  - (* tbool *) eauto using sem_typed_bool.
  - (* tvar  *) eauto using sem_typed_var.
  - (* tabs  *) eauto using sem_typed_abs.
  - (* tapp  *) eauto using sem_typed_app.
  - (* ttabs *) eauto using sem_typed_tabs.
  - (* ttapp *) eauto using sem_typed_tapp.
Qed.


(*** Examples ***)

(* Basic boolean example *)
Example ex_bool:
  typeof [] (tbool true) = Some TBool.
Proof. reflexivity. Qed.

Example ex_bool_eval:
  eval 10 [] (tbool true) = Some (Some (vbool true)).
Proof. reflexivity. Qed.

(* Identity function: \x:Bool. x *)
Example ex_id_bool:
  typeof [] (tabs TBool (tvar 0)) = Some (TFun TBool TBool).
Proof. reflexivity. Qed.

Example ex_id_bool_eval:
  eval 10 [] (tabs TBool (tvar 0)) = Some (Some (vabs [] (tvar 0))).
Proof. reflexivity. Qed.

(* Application of identity function: (\x:Bool. x) true *)
Example ex_id_app:
  typeof [] (tapp (tabs TBool (tvar 0)) (tbool true)) = Some TBool.
Proof. reflexivity. Qed.

Example ex_id_app_eval:
  eval 10 [] (tapp (tabs TBool (tvar 0)) (tbool true)) = Some (Some (vbool true)).
Proof. reflexivity. Qed.

(* Polymorphic identity function: /\X. \x:X. x *)
Example ex_poly_id:
  typeof [] (ttabs (tabs (TVar 0) (tvar 0))) = Some (TForall (TFun (TVar 0) (TVar 0))).
Proof. reflexivity. Qed.

Example ex_poly_id_eval:
  eval 10 [] (ttabs (tabs (TVar 0) (tvar 0))) = Some (Some (vtabs [] (tabs (TVar 0) (tvar 0)))).
Proof. reflexivity. Qed.

(* Type application of polymorphic identity: (/\X. \x:X. x)[Bool] *)
Example ex_poly_id_tapp:
  typeof [] (ttapp (ttabs (tabs (TVar 0) (tvar 0))) TBool) = Some (TFun TBool TBool).
Proof. reflexivity. Qed.

Example ex_poly_id_tapp_eval:
  eval 10 [] (ttapp (ttabs (tabs (TVar 0) (tvar 0))) TBool) = Some (Some (vabs [] (tvar 0))).
Proof. reflexivity. Qed.

(* Full application: (/\X. \x:X. x)[Bool] true *)
Example ex_poly_id_full:
  typeof [] (tapp (ttapp (ttabs (tabs (TVar 0) (tvar 0))) TBool) (tbool true)) = Some TBool.
Proof. reflexivity. Qed.

Example ex_poly_id_full_eval:
  eval 10 [] (tapp (ttapp (ttabs (tabs (TVar 0) (tvar 0))) TBool) (tbool true)) = Some (Some (vbool true)).
Proof. reflexivity. Qed.

(* Higher-order function: \f:(Bool -> Bool). \x:Bool. f x *)
Example ex_hof:
  typeof [] (tabs (TFun TBool TBool) (tabs TBool (tapp (tvar 1) (tvar 0)))) = 
  Some (TFun (TFun TBool TBool) (TFun TBool TBool)).
Proof. reflexivity. Qed.

(* Polymorphic compose function: /\A./\B./\C. \f:B->C. \g:A->B. \x:A. f(g x) *)
Example ex_compose:
  typeof [] 
    (ttabs (ttabs (ttabs 
      (tabs (TFun (TVar 1) (TVar 2)) 
        (tabs (TFun (TVar 2) (TVar 1)) 
          (tabs (TVar 2) 
            (tapp (tvar 2) (tapp (tvar 1) (tvar 0))))))))) = 
  Some (TForall (TForall (TForall 
    (TFun (TFun (TVar 1) (TVar 2)) 
      (TFun (TFun (TVar 2) (TVar 1)) 
        (TFun (TVar 2) (TVar 2))))))).
Proof. reflexivity. Qed.

(* Church boolean true: /\A. \x:A. \y:A. x *)
Example ex_church_true:
  typeof []
    (ttabs (tabs (TVar 0) (tabs (TVar 0) (tvar 1)))) =
  Some (TForall (TFun (TVar 0) (TFun (TVar 0) (TVar 0)))).
Proof. reflexivity. Qed.

(* Church boolean false: /\A. \x:A. \y:A. y *)
Example ex_church_false:
  typeof []
    (ttabs (tabs (TVar 0) (tabs (TVar 0) (tvar 0)))) =
  Some (TForall (TFun (TVar 0) (TFun (TVar 0) (TVar 0)))).
Proof. reflexivity. Qed.

(* Using Church true with Bool: (/\A. \x:A. \y:A. x)[Bool] true false *)
Example ex_church_true_app:
  typeof []
    (tapp (tapp (ttapp (ttabs (tabs (TVar 0) (tabs (TVar 0) (tvar 1)))) TBool) 
                       (tbool true)) 
               (tbool false)) = 
  Some TBool.
Proof. reflexivity. Qed.

Example ex_church_true_app_eval:
  eval 20 []
    (tapp (tapp (ttapp (ttabs (tabs (TVar 0) (tabs (TVar 0) (tvar 1)))) TBool) 
                       (tbool true)) 
               (tbool false)) = 
  Some (Some (vbool true)).
Proof. reflexivity. Qed.

(* Nested polymorphism: /\A. \f:(/\B. B -> A). f[A] *)
Example ex_nested_poly:
  typeof []
    (ttabs (tabs (TForall (TFun (TVar 0) (TVar 1))) 
                 (ttapp (tvar 0) (TVar 0)))) =
  Some (TForall (TFun (TForall (TFun (TVar 0) (TVar 1))) (TFun (TVar 0) (TVar 0)))).
Proof. reflexivity. Qed.

(* Type error example: applying function to wrong type *)
Example ex_type_error:
  typeof [] (tapp (tabs TBool (tvar 0)) (tabs TBool (tvar 0))) = None.
Proof. reflexivity. Qed.
