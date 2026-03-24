From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Psatz.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.InterpShiftLemmas.
Require Import RefinementTypes.InterpSubstLemmas.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.WfLemmas.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.PositivityLemmas.
Require Import RefinementTypes.SemanticImplies.

Definition sem_subtype (tbounds: TBounds) (tenv: list Ty) (facts: list ((nat * Term) * (nat * Term))) (A B: Ty) : Prop :=
  forall tvars venv,
    wf_env tvars tenv venv ->
    wf_benv tvars tbounds venv ->
    wf_facts venv facts ->
    forall v, interp tvars venv A v -> interp tvars venv B v.

Lemma sem_subtype_refl: forall tbounds tenv facts A,
  sem_subtype tbounds tenv facts A A.
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp. exact Hinterp.
Qed.

Lemma sem_subtype_trans: forall tbounds tenv facts A B C,
  sem_subtype tbounds tenv facts A B ->
  sem_subtype tbounds tenv facts B C ->
  sem_subtype tbounds tenv facts A C.
Proof.
  intros * HsubAB HsubBC tvars venv Henv Hbenv Hfacts v HinterpA.
  apply (HsubBC tvars venv Henv Hbenv Hfacts).
  apply (HsubAB tvars venv Henv Hbenv Hfacts).
  exact HinterpA.
Qed.

(** S-Fun: contravariant in domain, covariant in codomain. *)
Lemma sem_subtype_fun: forall tbounds tenv facts A1 A2 B1 B2,
  sem_subtype tbounds tenv facts B1 A1 ->
  sem_subtype (tbounds_shift_term tbounds) (A1 :: tenv) facts A2 B2 ->
  sem_subtype tbounds tenv facts (TFun A1 A2) (TFun B1 B2).
Proof.
  intros * HsubBA HsubAB tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in *. unfold interp_fun in *.
  destruct Hinterp as (venv' & body & Heq & Hbody).
  exists venv', body. split; [exact Heq|].
  intros arg Harg.
  apply (HsubBA tvars venv Henv Hbenv Hfacts) in Harg.
  specialize (Hbody _ Harg).
  unfold term_has_semtype in *.
  intros fuel r Heval. destruct (Hbody fuel r Heval) as [v' [Hv' Hty]].
  exists v'. split; [exact Hv'|].
  apply (HsubAB tvars (arg :: venv)).
  - apply wf_env_cons; assumption.
  - apply wf_benv_shift_term. exact Hbenv.
  - apply wf_facts_extend. exact Hfacts.
  - exact Hty.
Qed.

(** S-Forall: contravariant in lower bound, covariant in upper bound and body.
    The body subtyping is checked with the type variable bounded by [L2..U2]. *)
Lemma sem_subtype_forall: forall tbounds tenv facts L1 U1 L2 U2 A B,
  sem_subtype tbounds tenv facts L1 L2 ->
  sem_subtype tbounds tenv facts U2 U1 ->
  sem_subtype ((L2, U2) :: tbounds) (tenv_shift_type tenv) facts A B ->
  sem_subtype tbounds tenv facts (TForall L1 U1 A) (TForall L2 U2 B).
Proof.
  intros * HsubL HsubU HsubAB tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in *. unfold interp_forall in *.
  destruct Hinterp as (env' & body & Heq & Hbody).
  exists env', body. split; [exact Heq|].
  intros A' HL' HU'.
  assert (HL1 : forall w, interp tvars venv L1 w -> A' w).
  { intros w Hw. apply HL'. apply (HsubL tvars venv Henv Hbenv Hfacts). exact Hw. }
  assert (HU1 : forall w, A' w -> interp tvars venv U1 w).
  { intros w Hw. apply (HsubU tvars venv Henv Hbenv Hfacts). apply HU'. exact Hw. }
  specialize (Hbody A' HL1 HU1). unfold term_has_semtype in *.
  intros fuel r Heval. destruct (Hbody fuel r Heval) as [v' [Hv' Hty]].
  exists v'. split; [exact Hv'|].
  apply (HsubAB (A' :: tvars) venv).
  - apply env_incr_wf. exact Henv.
  - apply wf_benv_cons; assumption.
  - exact Hfacts.
  - exact Hty.
Qed.

(** ** Sigma type subtyping rule *)

(** S-Sigma: covariant in both components *)
Lemma sem_subtype_sigma: forall tbounds tenv facts A1 A2 B1 B2,
  sem_subtype tbounds tenv facts A1 B1 ->
  sem_subtype (tbounds_shift_term tbounds) (A1 :: tenv) facts A2 B2 ->
  sem_subtype tbounds tenv facts (TSigma A1 A2) (TSigma B1 B2).
Proof.
  intros * HsubA HsubB tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in *. unfold interp_sigma in *.
  destruct Hinterp as (v1 & v2 & Heq & Ha & Hb).
  exists v1, v2. split; [exact Heq|]. split.
  - apply (HsubA tvars venv Henv Hbenv Hfacts). exact Ha.
  - apply (HsubB tvars (v1 :: venv)).
    + apply wf_env_cons; assumption.
    + apply wf_benv_shift_term. exact Hbenv.
    + apply wf_facts_extend. exact Hfacts.
    + exact Hb.
Qed.

(** ** Union type subtyping rules *)

(** S-OrL: A <: A \/ B *)
Lemma sem_subtype_or_l: forall tbounds tenv facts A B,
  sem_subtype tbounds tenv facts A (TOr A B).
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl. unfold interp_or. left. exact Hinterp.
Qed.

(** S-OrR: B <: A \/ B *)
Lemma sem_subtype_or_r: forall tbounds tenv facts A B,
  sem_subtype tbounds tenv facts B (TOr A B).
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl. unfold interp_or. right. exact Hinterp.
Qed.

(** S-Or: If A <: C and B <: C, then A \/ B <: C *)
Lemma sem_subtype_or: forall tbounds tenv facts A B C,
  sem_subtype tbounds tenv facts A C ->
  sem_subtype tbounds tenv facts B C ->
  sem_subtype tbounds tenv facts (TOr A B) C.
Proof.
  intros * HsubA HsubB tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in Hinterp. unfold interp_or in Hinterp.
  destruct Hinterp as [Ha | Hb].
  - apply (HsubA tvars venv Henv Hbenv Hfacts). exact Ha.
  - apply (HsubB tvars venv Henv Hbenv Hfacts). exact Hb.
Qed.

(** ** Intersection type subtyping rules *)

(** S-AndL: A /\ B <: A *)
Lemma sem_subtype_and_l: forall tbounds tenv facts A B,
  sem_subtype tbounds tenv facts (TAnd A B) A.
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in Hinterp. unfold interp_and in Hinterp.
  exact (proj1 Hinterp).
Qed.

(** S-AndR: A /\ B <: B *)
Lemma sem_subtype_and_r: forall tbounds tenv facts A B,
  sem_subtype tbounds tenv facts (TAnd A B) B.
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in Hinterp. unfold interp_and in Hinterp.
  exact (proj2 Hinterp).
Qed.

(** S-And: If C <: A and C <: B, then C <: A /\ B *)
Lemma sem_subtype_and: forall tbounds tenv facts A B C,
  sem_subtype tbounds tenv facts C A ->
  sem_subtype tbounds tenv facts C B ->
  sem_subtype tbounds tenv facts C (TAnd A B).
Proof.
  intros * HsubA HsubB tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl. unfold interp_and. split.
  - apply (HsubA tvars venv Henv Hbenv Hfacts). exact Hinterp.
  - apply (HsubB tvars venv Henv Hbenv Hfacts). exact Hinterp.
Qed.

(** ** Refinement type subtyping rules *)

(** S-RefineBase: {x : A | p} <: A.
    A refinement type is a subtype of its base type. *)
Lemma sem_subtype_refine_base: forall tbounds tenv facts A p,
  sem_subtype tbounds tenv facts (TRefine A p) A.
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in Hinterp. unfold interp_refine in Hinterp.
  exact (proj1 Hinterp).
Qed.

(** S-Refine: {x : A | p1} <: {x : B | p2} when A <: B and p1 implies p2. *)
Lemma sem_subtype_refine: forall tbounds tenv facts A B p1 p2,
  sem_subtype tbounds tenv facts A B ->
  sem_implies (tbounds_shift_term tbounds) (A :: tenv) facts p1 p2 ->
  sem_subtype tbounds tenv facts (TRefine A p1) (TRefine B p2).
Proof.
  intros * HsubAB Himpl tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in *. unfold interp_refine in *.
  destruct Hinterp as [Ha Hp1].
  split.
  - apply (HsubAB tvars venv Henv Hbenv Hfacts). exact Ha.
  - apply (Himpl tvars (v :: venv)).
    + apply wf_env_cons; assumption.
    + apply wf_benv_shift_term. exact Hbenv.
    + apply wf_facts_extend. exact Hfacts.
    + exact Hp1.
Qed.

(** ** Top and Bottom type subtyping rules *)

(** S-Top: A <: Top for all A *)
Lemma sem_subtype_top: forall tbounds tenv facts A,
  sem_subtype tbounds tenv facts A TTop.
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp. exact I.
Qed.

(** S-Bot: Bot <: A for all A *)
Lemma sem_subtype_bot: forall tbounds tenv facts A,
  sem_subtype tbounds tenv facts TBot A.
Proof.
  intros * tvars venv Henv Hbenv Hfacts v Hinterp. contradiction.
Qed.

(** ** Type variable bound extraction rules *)

(** S-TVar-Upper: if type variable [i] has upper bound [U], then
    [TVar i <: shift U]. The bound is shifted by [S i] to account
    for the type variables introduced after it. *)
Lemma sem_subtype_tvar_upper: forall tbounds tenv facts i L U,
  nth_error tbounds i = Some (L, U) ->
  sem_subtype tbounds tenv facts (TVar i) (ren_ty (fun n => n + S i) id U).
Proof.
  intros * Hnth tvars venv Henv Hbenv Hfacts v Hinterp.
  destruct (wf_benv_lookup tvars tbounds venv i L U Hbenv Hnth)
    as [A [HnthA [HL HU]]].
  simpl in Hinterp. unfold interp_var in Hinterp.
  rewrite HnthA in Hinterp.
  apply HU in Hinterp.
  rewrite <- interp_shift_type_by.
  - exact Hinterp.
  - assert (i < length tvars) by (apply nth_error_Some; rewrite HnthA; discriminate).
    lia.
Qed.

(** S-TVar-Lower: if type variable [i] has lower bound [L], then
    [shift L <: TVar i]. *)
Lemma sem_subtype_tvar_lower: forall tbounds tenv facts i L U,
  nth_error tbounds i = Some (L, U) ->
  sem_subtype tbounds tenv facts (ren_ty (fun n => n + S i) id L) (TVar i).
Proof.
  intros * Hnth tvars venv Henv Hbenv Hfacts v Hinterp.
  destruct (wf_benv_lookup tvars tbounds venv i L U Hbenv Hnth)
    as [A [HnthA [HL HU]]].
  simpl. unfold interp_var. rewrite HnthA.
  apply HL.
  rewrite <- interp_shift_type_by in Hinterp.
  - exact Hinterp.
  - assert (i < length tvars) by (apply nth_error_Some; rewrite HnthA; discriminate).
    lia.
Qed.

(** ** Recursive type subtyping rules *)

(** S-Mu-Unfold: TMuAll A <: A[X := TMuAll A].
    Unfolding a positive recursive type yields a subtype. *)
Lemma sem_subtype_mu_unfold: forall tbounds tenv facts A,
  spos 0 A = true ->
  sem_subtype tbounds tenv facts (TMuAll A) (ty_subst A (TMuAll A)).
Proof.
  intros * Hspos tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl in Hinterp.
  set (F := fun (X: SemTy) => interp (X :: tvars) venv A) in *.
  rewrite <- interp_subst. fold F.
  apply (interp_spos_distribute A [] tvars venv (fun n => interp_mu n F) v).
  - exact Hspos.
  - intros n. exact (Hinterp (S n)).
Qed.

(** S-Mu-Fold: A[X := TMuAll A] <: TMuAll A.
    Folding back into a positive recursive type yields a subtype. *)
Lemma sem_subtype_mu_fold: forall tbounds tenv facts A,
  spos 0 A = true ->
  sem_subtype tbounds tenv facts (ty_subst A (TMuAll A)) (TMuAll A).
Proof.
  intros * Hspos tvars venv Henv Hbenv Hfacts v Hinterp.
  simpl.
  set (F := fun (X: SemTy) => interp (X :: tvars) venv A).
  rewrite <- interp_subst in Hinterp. fold F in Hinterp.
  intro n. destruct n as [|n'].
  - simpl. trivial.
  - simpl.
    eapply (interp_spos_mono A [] tvars venv
              (fun w => forall m, interp_mu m F w)
              (interp_mu n' F) v).
    + exact Hspos.
    + intros w Hw. apply Hw.
    + exact Hinterp.
Qed.
