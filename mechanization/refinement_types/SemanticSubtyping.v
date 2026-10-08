(** * Semantic Subtyping (§3.5, Figures 8 and 10)

    The semantic subtyping judgment Γ ⊨ A <: B ([sem_subtype], Figure 8),
    and one soundness lemma per subtyping rule of Figure 10. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Psatz.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.InterpLemmas.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.WfLemmas.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.PositivityLemmas.
Require Import RefinementTypes.SemanticImplies.

(** ** The judgment (Figure 8) *)

(** [A] is a semantic subtype of [B] if, in every well-formed environment,
    every value in the interpretation of [A] is in the interpretation of
    [B]. *)
Definition sem_subtype (gamma: Ctx) (A B: Ty) : Prop :=
  forall tvars venv,
    wf_ctx tvars gamma venv ->
    forall v, interp tvars venv A v -> interp tvars venv B v.

(** ** Reflexivity and transitivity *)

(** S-Refl *)
Lemma sem_subtype_refl: forall gamma A,
  sem_subtype gamma A A.
Proof.
  intros gamma A tvars venv Hwf v Hinterp. exact Hinterp.
Qed.

(** S-Trans *)
Lemma sem_subtype_trans: forall gamma A B C,
  sem_subtype gamma A B ->
  sem_subtype gamma B C ->
  sem_subtype gamma A C.
Proof.
  intros gamma A B C HsubAB HsubBC tvars venv Hwf v HinterpA.
  apply (HsubBC tvars venv Hwf).
  apply (HsubAB tvars venv Hwf).
  exact HinterpA.
Qed.

(** ** Function and universal type subtyping rules *)

(** S-Fun: contravariant in domain, covariant in codomain. *)
Lemma sem_subtype_fun: forall gamma A1 A2 B1 B2,
  sem_subtype gamma B1 A1 ->
  sem_subtype (ctx_cons_term gamma A1) A2 B2 ->
  sem_subtype gamma (TFun A1 A2) (TFun B1 B2).
Proof.
  intros gamma A1 A2 B1 B2 HsubBA HsubAB tvars venv Hwf v Hinterp.
  simpl in *. unfold interp_fun in *.
  destruct Hinterp as (venv' & body & Heq & Hbody).
  exists venv', body. split; [exact Heq|].
  intros arg Harg.
  apply (HsubBA tvars venv Hwf) in Harg.
  eapply term_has_semtype_mono; [| exact (Hbody arg Harg)].
  apply (HsubAB tvars (arg :: venv)). apply wf_ctx_cons_term; assumption.
Qed.

(** S-Forall: contravariant in lower bound, covariant in upper bound and body.
    The body subtyping is checked with the type variable bounded by [L2..U2]. *)
Lemma sem_subtype_forall: forall gamma L1 U1 L2 U2 A B,
  sem_subtype gamma L1 L2 ->
  sem_subtype gamma U2 U1 ->
  sem_subtype (ctx_cons_type gamma L2 U2) A B ->
  sem_subtype gamma (TForall L1 U1 A) (TForall L2 U2 B).
Proof.
  intros gamma L1 U1 L2 U2 A B HsubL HsubU HsubAB tvars venv Hwf v Hinterp.
  simpl in *. unfold interp_forall in *.
  destruct Hinterp as (env' & body & Heq & Hbody).
  exists env', body. split; [exact Heq|].
  intros X HL HU.
  assert (HL1 : forall w, interp tvars venv L1 w -> X w).
  { intros w Hw. apply HL. apply (HsubL tvars venv Hwf). exact Hw. }
  assert (HU1 : forall w, X w -> interp tvars venv U1 w).
  { intros w Hw. apply (HsubU tvars venv Hwf). apply HU. exact Hw. }
  eapply term_has_semtype_mono; [| exact (Hbody X HL1 HU1)].
  apply (HsubAB (X :: tvars) venv). apply wf_ctx_cons_type; assumption.
Qed.

(** ** Sigma type subtyping rule *)

(** S-Sigma: covariant in both components *)
Lemma sem_subtype_sigma: forall gamma A1 A2 B1 B2,
  sem_subtype gamma A1 B1 ->
  sem_subtype (ctx_cons_term gamma A1) A2 B2 ->
  sem_subtype gamma (TSigma A1 A2) (TSigma B1 B2).
Proof.
  intros gamma A1 A2 B1 B2 HsubA HsubB tvars venv Hwf v Hinterp.
  simpl in *. unfold interp_sigma in *.
  destruct Hinterp as (v1 & v2 & Heq & Ha & Hb).
  exists v1, v2. split; [exact Heq|]. split.
  - apply (HsubA tvars venv Hwf). exact Ha.
  - apply (HsubB tvars (v1 :: venv)); [apply wf_ctx_cons_term; assumption | exact Hb].
Qed.

(** ** Union type subtyping rules *)

(** S-OrL: A <: A \/ B *)
Lemma sem_subtype_or_l: forall gamma A B,
  sem_subtype gamma A (TOr A B).
Proof.
  intros gamma A B tvars venv Hwf v Hinterp. simpl. unfold interp_or. left. exact Hinterp.
Qed.

(** S-OrR: B <: A \/ B *)
Lemma sem_subtype_or_r: forall gamma A B,
  sem_subtype gamma B (TOr A B).
Proof.
  intros gamma A B tvars venv Hwf v Hinterp. simpl. unfold interp_or. right. exact Hinterp.
Qed.

(** S-Or: If A <: C and B <: C, then A \/ B <: C *)
Lemma sem_subtype_or: forall gamma A B C,
  sem_subtype gamma A C ->
  sem_subtype gamma B C ->
  sem_subtype gamma (TOr A B) C.
Proof.
  intros gamma A B C HsubA HsubB tvars venv Hwf v [Ha | Hb].
  - apply (HsubA tvars venv Hwf). exact Ha.
  - apply (HsubB tvars venv Hwf). exact Hb.
Qed.

(** ** Intersection type subtyping rules *)

(** S-AndL: A /\ B <: A *)
Lemma sem_subtype_and_l: forall gamma A B,
  sem_subtype gamma (TAnd A B) A.
Proof.
  intros gamma A B tvars venv Hwf v [Ha _]. exact Ha.
Qed.

(** S-AndR: A /\ B <: B *)
Lemma sem_subtype_and_r: forall gamma A B,
  sem_subtype gamma (TAnd A B) B.
Proof.
  intros gamma A B tvars venv Hwf v [_ Hb]. exact Hb.
Qed.

(** S-And: If C <: A and C <: B, then C <: A /\ B *)
Lemma sem_subtype_and: forall gamma A B C,
  sem_subtype gamma C A ->
  sem_subtype gamma C B ->
  sem_subtype gamma C (TAnd A B).
Proof.
  intros gamma A B C HsubA HsubB tvars venv Hwf v Hinterp. split.
  - apply (HsubA tvars venv Hwf). exact Hinterp.
  - apply (HsubB tvars venv Hwf). exact Hinterp.
Qed.

(** ** Refinement type subtyping rules *)

(** S-RefineBase: {x : A | p} <: A.
    A refinement type is a subtype of its base type. *)
Lemma sem_subtype_refine_base: forall gamma A p,
  sem_subtype gamma (TRefine A p) A.
Proof.
  intros gamma A p tvars venv Hwf v [Ha _]. exact Ha.
Qed.

(** S-Refine: {x : A | p1} <: {x : B | p2} when A <: B and p1 implies p2. *)
Lemma sem_subtype_refine: forall gamma A B p1 p2,
  sem_subtype gamma A B ->
  sem_implies (ctx_cons_term gamma A) p1 p2 ->
  sem_subtype gamma (TRefine A p1) (TRefine B p2).
Proof.
  intros gamma A B p1 p2 HsubAB Himpl tvars venv Hwf v [Ha Hp1]. split.
  - apply (HsubAB tvars venv Hwf). exact Ha.
  - apply (Himpl tvars (v :: venv)); [apply wf_ctx_cons_term; assumption | exact Hp1].
Qed.

(** ** Top and Bottom type subtyping rules *)

(** S-Top: A <: Top for all A *)
Lemma sem_subtype_top: forall gamma A,
  sem_subtype gamma A TTop.
Proof.
  intros gamma A tvars venv Hwf v Hinterp. exact I.
Qed.

(** S-Bot: Bot <: A for all A *)
Lemma sem_subtype_bot: forall gamma A,
  sem_subtype gamma TBot A.
Proof.
  intros gamma A tvars venv Hwf v Hinterp. contradiction.
Qed.

(** ** Type variable bound extraction rules *)

(** S-TVar-Upper: if type variable [i] has upper bound [U], then
    [TVar i <: shift U]. The bound is shifted by [S i] to account
    for the type variables introduced after it. *)
Lemma sem_subtype_tvar_upper: forall gamma i L U,
  nth_error (ctx_tbounds gamma) i = Some (L, U) ->
  sem_subtype gamma (TVar i) (ren_ty (fun n => n + S i) id U).
Proof.
  intros gamma i L U Hnth tvars venv Hwf v Hinterp.
  destruct (wf_ctx_lookup_type _ _ _ _ _ _ Hwf Hnth) as [X [HnthX [HL HU]]].
  simpl in Hinterp. unfold interp_var in Hinterp. rewrite HnthX in Hinterp.
  apply HU in Hinterp.
  rewrite <- interp_shift_type_by; [exact Hinterp |].
  assert (i < length tvars) by (apply nth_error_Some; rewrite HnthX; discriminate).
  lia.
Qed.

(** S-TVar-Lower: if type variable [i] has lower bound [L], then
    [shift L <: TVar i]. *)
Lemma sem_subtype_tvar_lower: forall gamma i L U,
  nth_error (ctx_tbounds gamma) i = Some (L, U) ->
  sem_subtype gamma (ren_ty (fun n => n + S i) id L) (TVar i).
Proof.
  intros gamma i L U Hnth tvars venv Hwf v Hinterp.
  destruct (wf_ctx_lookup_type _ _ _ _ _ _ Hwf Hnth) as [X [HnthX [HL HU]]].
  simpl. unfold interp_var. rewrite HnthX.
  apply HL.
  rewrite <- interp_shift_type_by in Hinterp; [exact Hinterp |].
  assert (i < length tvars) by (apply nth_error_Some; rewrite HnthX; discriminate).
  lia.
Qed.

(** ** Recursive type subtyping rules *)

(** S-Mu-Unfold: TMuAll A <: A[X := TMuAll A].
    Unfolding a positive recursive type yields a subtype. *)
Lemma sem_subtype_mu_unfold: forall gamma A,
  spos 0 A = true ->
  sem_subtype gamma (TMuAll A) (ty_subst A (TMuAll A)).
Proof.
  intros gamma A Hspos tvars venv Hwf v Hinterp.
  simpl in Hinterp.
  set (F := fun (X: SemTy) => interp (X :: tvars) venv A) in *.
  rewrite <- interp_subst. fold F.
  apply (interp_spos_distribute A [] tvars venv (fun n => interp_mu n F) v).
  - exact Hspos.
  - intros n. exact (Hinterp (S n)).
Qed.

(** S-Mu-Fold: A[X := TMuAll A] <: TMuAll A.
    Folding back into a positive recursive type yields a subtype. *)
Lemma sem_subtype_mu_fold: forall gamma A,
  spos 0 A = true ->
  sem_subtype gamma (ty_subst A (TMuAll A)) (TMuAll A).
Proof.
  intros gamma A Hspos tvars venv Hwf v Hinterp.
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
