(** * Avoidance Soundness (Lemma 3.8)

    This file proves that avoidance approximates in the right direction:
    - Positive polarity yields a supertype:
      [interp T v -> interp (avoid Pos i T) v]
    - Negative polarity yields a subtype:
      [interp (avoid Neg i T) v -> interp T v]

    The key insight is that when we replace a refinement predicate with
    [true], we get a supertype (any value satisfying the refinement also
    satisfies "true"). When we replace with [false], we get a subtype
    (no value satisfies "false", so it's vacuously true). *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Psatz.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.InterpShiftLemmas.
Require Import RefinementTypes.Avoid.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.PositivityLemmas.

(** Helper: evaluating [false] never gives [true] *)
Lemma eval_false_not_true: forall fuel venv,
  eval fuel venv (tbool false) <> Some (Some (vbool true)).
Proof.
  intros fuel venv. destruct fuel; simpl; discriminate.
Qed.

(** ** Avoidance preserves positivity *)

(** If spos/ty_var_absent is true for T, it remains true for avoid pol j T.
    Must be proved simultaneously since spos uses ty_var_absent. *)
Lemma spos_ty_var_absent_avoid: forall T pol j k,
  (spos k T = true -> spos k (avoid pol j T) = true) /\
  (ty_var_absent k T = true -> ty_var_absent k (avoid pol j T) = true).
Proof.
  induction T; intros pol j k; split; intro H; simpl in H |- *; try exact H.
  (* TFun - spos *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj1 (IHT2 _ _ _) H2).
  (* TFun - ty_var_absent *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
  (* TForall - spos *)
  - apply andb_true_iff in H as [H12 H3].
    apply andb_true_iff in H12 as [H1 H2].
    apply andb_true_iff. split; [apply andb_true_iff; split |].
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
    + exact (proj1 (IHT3 _ _ _) H3).
  (* TForall - ty_var_absent *)
  - apply andb_true_iff in H as [H12 H3].
    apply andb_true_iff in H12 as [H1 H2].
    apply andb_true_iff. split; [apply andb_true_iff; split |].
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
    + exact (proj2 (IHT3 _ _ _) H3).
  (* TRefine - spos *)
  - destruct (term_mentions (S j) t); destruct pol; simpl;
    exact (proj1 (IHT _ _ _) H).
  (* TRefine - ty_var_absent *)
  - destruct (term_mentions (S j) t); destruct pol; simpl;
    exact (proj2 (IHT _ _ _) H).
  (* TSigma - spos *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj1 (IHT1 _ _ _) H1).
    + exact (proj1 (IHT2 _ _ _) H2).
  (* TSigma - ty_var_absent *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
  (* TSum - spos *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj1 (IHT1 _ _ _) H1).
    + exact (proj1 (IHT2 _ _ _) H2).
  (* TSum - ty_var_absent *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
  (* TOr - spos: uses ty_var_absent *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
  (* TOr - ty_var_absent *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
  (* TAnd - spos *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj1 (IHT1 _ _ _) H1).
    + exact (proj1 (IHT2 _ _ _) H2).
  (* TAnd - ty_var_absent *)
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    + exact (proj2 (IHT1 _ _ _) H1).
    + exact (proj2 (IHT2 _ _ _) H2).
  (* TMuAll - spos: spos k (TMuAll B) = spos 0 B && ty_var_absent (S k) B *)
  - apply andb_true_iff in H as [Hs Hab].
    rewrite Hs. simpl. apply andb_true_iff. split.
    + exact (proj1 (IHT _ _ _) Hs).
    + exact (proj2 (IHT _ _ _) Hab).
  (* TMuAll - ty_var_absent: ty_var_absent k (TMuAll B) = ty_var_absent (S k) B *)
  - destruct (spos 0 T) eqn:Hs; simpl.
    + exact (proj2 (IHT _ _ _) H).
    + destruct pol; reflexivity.
Qed.

Definition spos_avoid T pol j k := proj1 (spos_ty_var_absent_avoid T pol j k).

(** ** Avoidance soundness (Lemma 3.8) *)

(** Combined avoidance lemma: both directions proven simultaneously.

    The positive and negative directions must be proven together because
    of the contravariance of function types: TFun's domain flips polarity. *)

Lemma interp_avoid_pos_neg: forall T tvars venv val i,
  (interp tvars venv T val ->
   interp tvars venv (avoid Pos i T) val) /\
  (interp tvars venv (avoid Neg i T) val ->
   interp tvars venv T val).
Proof.
  induction T as [X | | | | A IHA B IHB | L IHL U IHU B IHB | A IHA p | A IHA B IHB
    | A IHA B IHB | A IHA B IHB | A IHA B IHB | | | B IHB];
    intros tvars venv val i; split; simpl; intro H; try exact H.
  (* TFun - pos *)
  - unfold interp_fun in *.
    destruct H as (venv' & body & Heq & Hbody).
    exists venv', body. split; [exact Heq|]. intros arg Harg.
    apply (proj2 (IHA tvars venv arg i)) in Harg.
    specialize (Hbody _ Harg). unfold term_has_semtype in *.
    intros fuel r Heval. destruct (Hbody fuel r Heval) as [v [Hv Hty]].
    exists v. split; [exact Hv|]. exact (proj1 (IHB tvars (arg :: venv) v (S i)) Hty).
  (* TFun - neg *)
  - unfold interp_fun in *.
    destruct H as (venv' & body & Heq & Hbody).
    exists venv', body. split; [exact Heq|]. intros arg Harg.
    apply (proj1 (IHA tvars venv arg i)) in Harg.
    specialize (Hbody _ Harg). unfold term_has_semtype in *.
    intros fuel r Heval. destruct (Hbody fuel r Heval) as [v [Hv Hty]].
    exists v. split; [exact Hv|]. exact (proj2 (IHB tvars (arg :: venv) v (S i)) Hty).
  (* TForall - pos *)
  - unfold interp_forall in *.
    destruct H as (env' & body & Heq & Hbody).
    exists env', body. split; [exact Heq|]. intros A' HL' HU'.
    assert (HL2 : forall w, interp tvars venv L w -> A' w).
    { intros w Hw. apply HL'. exact (proj1 (IHL tvars venv w i) Hw). }
    assert (HU2 : forall w, A' w -> interp tvars venv U w).
    { intros w Hw. exact (proj2 (IHU tvars venv w i) (HU' w Hw)). }
    specialize (Hbody A' HL2 HU2). unfold term_has_semtype in *.
    intros fuel r Heval. destruct (Hbody fuel r Heval) as [v [Hv Hty]].
    exists v. split; [exact Hv|]. exact (proj1 (IHB (A' :: tvars) venv v i) Hty).
  (* TForall - neg *)
  - unfold interp_forall in *.
    destruct H as (env' & body & Heq & Hbody).
    exists env', body. split; [exact Heq|]. intros A' HL' HU'.
    assert (HL2 : forall w, interp tvars venv (avoid Neg i L) w -> A' w).
    { intros w Hw. apply HL'. exact (proj2 (IHL tvars venv w i) Hw). }
    assert (HU2 : forall w, A' w -> interp tvars venv (avoid Pos i U) w).
    { intros w Hw. exact (proj1 (IHU tvars venv w i) (HU' w Hw)). }
    specialize (Hbody A' HL2 HU2). unfold term_has_semtype in *.
    intros fuel r Heval. destruct (Hbody fuel r Heval) as [v [Hv Hty]].
    exists v. split; [exact Hv|]. exact (proj2 (IHB (A' :: tvars) venv v i) Hty).
  (* TRefine - pos *)
  - destruct (term_mentions (S i) p) eqn:Hm.
    + simpl. destruct H as [HA Hp]. split.
      * exact (proj1 (IHA tvars venv val i) HA).
      * unfold eval_to_true, term_has_semtype.
        intros fuel r Heval. destruct fuel; simpl in Heval; [discriminate|].
        inversion Heval; subst. exists (vbool true). auto.
    + simpl. destruct H as [HA Hp]. split.
      * exact (proj1 (IHA tvars venv val i) HA).
      * exact Hp.
  (* TRefine - neg *)
  - destruct (term_mentions (S i) p) eqn:Hm.
    + simpl in H. destruct H as [_ Hp]. exfalso.
      unfold eval_to_true, term_has_semtype in Hp.
      assert (Hprem: eval 1 (val :: venv) (tbool false) = Some (Some (vbool false))).
      { simpl. reflexivity. }
      destruct (Hp 1 (Some (vbool false)) Hprem) as [v [Hv Htrue]].
      subst v. discriminate.
    + simpl in H. destruct H as [HA Hp]. split.
      * exact (proj2 (IHA tvars venv val i) HA).
      * exact Hp.
  (* TSigma - pos *)
  - unfold interp_sigma in *.
    destruct H as (v1 & v2 & Heq & Ha & Hb).
    exists v1, v2. split; [exact Heq|]. split.
    + exact (proj1 (IHA tvars venv v1 i) Ha).
    + exact (proj1 (IHB tvars (v1 :: venv) v2 (S i)) Hb).
  (* TSigma - neg *)
  - unfold interp_sigma in *.
    destruct H as (v1 & v2 & Heq & Ha & Hb).
    exists v1, v2. split; [exact Heq|]. split.
    + exact (proj2 (IHA tvars venv v1 i) Ha).
    + exact (proj2 (IHB tvars (v1 :: venv) v2 (S i)) Hb).
  (* TSum - pos *)
  - unfold interp_sum in *. destruct H as [[w [Heq Ha]] | [w [Heq Hb]]].
    + left. exists w. split; [exact Heq|]. exact (proj1 (IHA tvars venv w i) Ha).
    + right. exists w. split; [exact Heq|]. exact (proj1 (IHB tvars venv w i) Hb).
  (* TSum - neg *)
  - unfold interp_sum in *. destruct H as [[w [Heq Ha]] | [w [Heq Hb]]].
    + left. exists w. split; [exact Heq|]. exact (proj2 (IHA tvars venv w i) Ha).
    + right. exists w. split; [exact Heq|]. exact (proj2 (IHB tvars venv w i) Hb).
  (* TOr - pos *)
  - unfold interp_or in *. destruct H as [Ha | Hb].
    + left. exact (proj1 (IHA tvars venv val i) Ha).
    + right. exact (proj1 (IHB tvars venv val i) Hb).
  (* TOr - neg *)
  - unfold interp_or in *. destruct H as [Ha | Hb].
    + left. exact (proj2 (IHA tvars venv val i) Ha).
    + right. exact (proj2 (IHB tvars venv val i) Hb).
  (* TAnd - pos *)
  - unfold interp_and in *. destruct H as [Ha Hb]. split.
    + exact (proj1 (IHA tvars venv val i) Ha).
    + exact (proj1 (IHB tvars venv val i) Hb).
  (* TAnd - neg *)
  - unfold interp_and in *. destruct H as [Ha Hb]. split.
    + exact (proj2 (IHA tvars venv val i) Ha).
    + exact (proj2 (IHB tvars venv val i) Hb).
  (* TMuAll - pos *)
  - destruct (spos 0 B) eqn:Hspos.
    + (* spos 0 B = true: avoid recurses, use interp_mu_mono *)
      simpl. intro n.
      apply (interp_mu_mono n
        (fun X => interp (X :: tvars) venv B)
        (fun X => interp (X :: tvars) venv (avoid Pos i B))).
      * intros X v. exact (proj1 (IHB (X :: tvars) venv v i)).
      * intros S1 S2 Hsub w Hw.
        apply (interp_spos_mono (avoid Pos i B) [] tvars venv S1 S2 w
          (spos_avoid B Pos i 0 Hspos) Hsub Hw).
      * exact (H n).
    + (* spos 0 B = false: avoid gives TTop, goal is True *)
      exact I.
  (* TMuAll - neg *)
  - destruct (spos 0 B) eqn:Hspos.
    + (* spos 0 B = true: avoid recurses, use interp_mu_mono *)
      simpl in H. intro n.
      apply (interp_mu_mono n
        (fun X => interp (X :: tvars) venv (avoid Neg i B))
        (fun X => interp (X :: tvars) venv B)).
      * intros X v. exact (proj2 (IHB (X :: tvars) venv v i)).
      * intros S1 S2 Hsub w Hw.
        apply (interp_spos_mono B [] tvars venv S1 S2 w Hspos Hsub Hw).
      * exact (H n).
    + (* spos 0 B = false: avoid gives TBot, H is False *)
      simpl in H. contradiction.
Qed.

(** Extract the individual directions as separate lemmas. *)

Lemma interp_avoid_pos: forall T tvars venv val i,
  interp tvars venv T val ->
  interp tvars venv (avoid Pos i T) val.
Proof.
  intros. exact (proj1 (interp_avoid_pos_neg T tvars venv val i) H).
Qed.

Lemma interp_avoid_neg: forall T tvars venv val i,
  interp tvars venv (avoid Neg i T) val ->
  interp tvars venv T val.
Proof.
  intros. exact (proj2 (interp_avoid_pos_neg T tvars venv val i) H).
Qed.

(** Corollary: avoiding variable 0 in positive polarity gives a supertype *)
Lemma interp_avoid_var0: forall T tvars venv v,
  interp tvars venv T v ->
  interp tvars venv (avoid_var0 T) v.
Proof.
  intros. eapply interp_avoid_pos; exact H.
Qed.

(** ** Avoided types are closed under the avoided variable *)

(** Helper: substitution is identity on types/terms that don't mention a variable *)
Lemma subst_not_mentions_ty T : forall sigma i,
  (forall n, n <> i -> sigma n = tvar n) ->
  term_mentions_ty i T = false ->
  subst_ty TVar sigma T = T
with subst_not_mentions_tm t : forall sigma i,
  (forall n, n <> i -> sigma n = tvar n) ->
  term_mentions i t = false ->
  subst_tm TVar sigma t = t.
Proof.
  all: (destruct T || destruct t); intros sigma i Hsigma Hm; simpl in *.
  (* Trivial cases *)
  all: try reflexivity.
  (* tvar case: sigma n = tvar n from Hsigma *)
  all: try match goal with
    |- ?s ?n = tvar ?n =>
      apply Hsigma; intros ->; rewrite Nat.eqb_refl in Hm; discriminate
  end.
  (* Split boolean conjunctions in Hm *)
  all: try (apply orb_false_iff in Hm as [Hm1 Hm2]).
  all: try (apply orb_false_iff in Hm2 as [Hm2 Hm3]).
  all: try (apply orb_false_iff in Hm1 as [Hm1 Hm1']).
  (* Break down constructor equalities *)
  all: f_equal; try reflexivity.
  (* Direct recursion: same sigma, same i *)
  all: try (eapply subst_not_mentions_ty; [exact Hsigma | eassumption]).
  all: try (eapply subst_not_mentions_tm; [exact Hsigma | eassumption]).
  (* Cases with up_tm_tm sigma (TFun/TSigma/TRefine codomain, tabs/tlet body) *)
  all: try (rewrite subst_ty_up_tm_ty_TVar;
    apply (subst_not_mentions_ty _ _ (S i));
    [intros [|m] Hneq; [reflexivity|];
     unfold up_tm_tm, scons, funcomp; rewrite Hsigma; [reflexivity | lia]
    | eassumption]).
  all: try (rewrite subst_tm_up_tm_ty_TVar;
    apply (subst_not_mentions_tm _ _ (S i));
    [intros [|m] Hneq; [reflexivity|];
     unfold up_tm_tm, scons, funcomp; rewrite Hsigma; [reflexivity | lia]
    | eassumption]).
  (* Cases with up_ty_tm sigma (TForall body, ttabs body) *)
  all: try (etransitivity;
    [apply subst_ty_ext; [exact up_ty_ty_id | reflexivity] |];
    eapply subst_not_mentions_ty;
    [intros n Hne; unfold up_ty_tm, funcomp;
     rewrite Hsigma; [simpl; reflexivity | exact Hne]
    | eassumption]).
  all: try (etransitivity;
    [apply subst_tm_ext; [exact up_ty_ty_id | reflexivity] |];
    eapply subst_not_mentions_tm;
    [intros n Hne; unfold up_ty_tm, funcomp;
     rewrite Hsigma; [simpl; reflexivity | exact Hne]
    | eassumption]).
  (* tmatch_pair body: double up_tm_tm *)
  - etransitivity.
    { apply subst_tm_ext.
      - intro n. unfold up_tm_ty, funcomp. simpl. reflexivity.
      - reflexivity. }
    eapply subst_not_mentions_tm; [| eassumption].
    intros [|[|m]] Hneq; try reflexivity.
    unfold up_tm_tm, scons, funcomp.
    unfold up_tm_tm, scons, funcomp.
    rewrite Hsigma; [reflexivity | lia].
Qed.

(** Helper: up_tm_tm preserves the "identity except at i" property *)
Lemma up_tm_tm_not_i : forall sigma i,
  (forall n, n <> i -> sigma n = tvar n) ->
  forall n, n <> S i -> up_tm_tm sigma n = tvar n.
Proof.
  intros sigma i Hsigma [|m] Hneq.
  - reflexivity.
  - unfold up_tm_tm, scons, funcomp. rewrite Hsigma; [reflexivity | lia].
Qed.

(** The composition shift-after-scons is identity except at position i *)
Lemma shift_scons_comp_id : forall i z,
  let comp := fun n => subst_tm TVar (upn_tm i (fun m => tvar (S m)))
                                      (upn_tm i (z .: tvar) n) in
  forall n, n <> i -> comp n = tvar n.
Proof.
  intros i z comp n Hne. unfold comp.
  rewrite iter_up_tm.
  destruct (lt_dec n i) as [Hlt | Hge].
  - (* n < i: upn_tm i (z .: tvar) n = tvar n *)
    simpl. rewrite iter_up_tm.
    destruct (lt_dec n i); [reflexivity | lia].
  - (* n >= i, n <> i => n > i *)
    assert (Hgt : n > i) by lia.
    destruct (n - i) as [|m] eqn:Heq; [lia|].
    (* (z .: tvar) (S m) = tvar m *)
    (* ren_tm id (+i) (tvar m) = tvar (m + i) *)
    (* subst_tm TVar (upn_tm i shift) (tvar (m + i)) = upn_tm i shift (m + i) *)
    simpl. rewrite iter_up_tm.
    destruct (lt_dec (m + i) i); [lia|].
    replace (m + i - i) with m by lia.
    simpl. f_equal. lia.
Qed.

(** Avoided types don't mention the avoided variable *)
Lemma avoid_not_mentions : forall T pol i,
  term_mentions_ty i (avoid pol i T) = false.
Proof.
  induction T; intros pol i; simpl; auto.
  - (* TFun *) rewrite IHT1, IHT2. reflexivity.
  - (* TForall *) rewrite IHT1, IHT2, IHT3. reflexivity.
  - (* TRefine *)
    destruct (term_mentions (S i) t) eqn:Hm; destruct pol; simpl;
    rewrite IHT; simpl; try rewrite Hm; reflexivity.
  - (* TSigma *) rewrite IHT1, IHT2. reflexivity.
  - (* TSum *) rewrite IHT1, IHT2. reflexivity.
  - (* TOr *) rewrite IHT1, IHT2. reflexivity.
  - (* TAnd *) rewrite IHT1, IHT2. reflexivity.
  - (* TMuAll *) destruct (spos 0 T); [apply IHT | destruct pol; reflexivity].
Qed.

Lemma avoid_subst_shift_id_gen: forall T pol i z,
  subst_ty TVar (upn_tm i (fun n => tvar (S n)))
    (subst_ty TVar (upn_tm i (z .: tvar)) (avoid pol i T)) = avoid pol i T.
Proof.
  intros.
  rewrite subst_comp_ty.
  etransitivity.
  { apply subst_ty_ext.
    - intro n. unfold funcomp. simpl. reflexivity.
    - intro n. reflexivity. }
  apply (subst_not_mentions_ty _ _ i).
  - intros n Hne. unfold funcomp.
    apply shift_scons_comp_id. exact Hne.
  - apply avoid_not_mentions.
Qed.

Lemma avoid_subst_shift_id: forall T z,
  subst_ty TVar (fun n => tvar (S n))
    (subst_ty TVar (z .: tvar) (avoid_var0 T)) = avoid_var0 T.
Proof.
  intros. unfold avoid_var0.
  exact (avoid_subst_shift_id_gen T Pos 0 z).
Qed.

(** Semantic corollary: avoided types are invariant under subst-then-shift. *)
Lemma interp_avoid_shift: forall T tvars venv z,
  interp tvars venv (avoid_var0 T) =
  interp tvars venv
    (subst_ty TVar (fun n => tvar (S n))
      (subst_ty TVar (z .: tvar) (avoid_var0 T))).
Proof.
  intros. rewrite avoid_subst_shift_id. reflexivity.
Qed.
