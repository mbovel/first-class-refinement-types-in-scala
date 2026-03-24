(** * Positivity Lemmas

    Key results enabling fold/unfold for recursive types:
    - [term_has_semtype_mono]: term_has_semtype is monotone in the predicate
    - [interp_ty_var_absent]: interp is independent of absent type variables
    - [interp_spos_mono]: positive types are covariant (monotone)
    - [interp_spos_distribute]: universal quantifier commutes with positive contexts *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.Positivity.

(** ** term_has_semtype is monotone in its predicate *)

Lemma term_has_semtype_mono: forall venv t P Q,
  (forall v, P v -> Q v) ->
  term_has_semtype venv t P -> term_has_semtype venv t Q.
Proof.
  intros venv t P Q Hmono Htype.
  intros fuel r Heval.
  destruct (Htype fuel r Heval) as [v [Hr Hv]].
  exists v. split; [exact Hr | apply Hmono; exact Hv].
Qed.

(** Helper: transport a value along a function equality *)
Lemma transport_fun : forall (f g : Value -> Prop) v,
  f = g -> f v -> g v.
Proof. intros f g v Heq H. rewrite <- Heq. exact H. Qed.

Lemma transport_fun_rev : forall (f g : Value -> Prop) v,
  f = g -> g v -> f v.
Proof. intros f g v Heq H. rewrite Heq. exact H. Qed.

(** ** Interpretation is independent of absent type variables *)

Lemma interp_ty_var_absent: forall A tvars1 tvars2 venv S1 S2,
  ty_var_absent (length tvars1) A = true ->
  interp (tvars1 ++ S1 :: tvars2) venv A = interp (tvars1 ++ S2 :: tvars2) venv A.
Proof.
  induction A; intros tvars1 tvars2 venv S1 S2 Habsent;
    simpl in Habsent; try reflexivity.
  - (* TVar *)
    apply negb_true_iff in Habsent. apply Nat.eqb_neq in Habsent.
    simpl. apply functional_extensionality. intros val. unfold interp_var.
    destruct (lt_dec v (length tvars1)) as [Hlt | Hge].
    + rewrite !nth_error_app1 by lia. reflexivity.
    + rewrite !nth_error_app2 by lia.
      destruct (v - length tvars1) as [|k] eqn:Ek; [lia | reflexivity].
  - (* TFun *)
    apply andb_true_iff in Habsent. destruct Habsent as [HA HB].
    simpl. f_equal.
    + apply IHA1; auto.
    + apply functional_extensionality. intros arg. apply IHA2; auto.
  - (* TForall *)
    apply andb_true_iff in Habsent. destruct Habsent as [HLU HB].
    apply andb_true_iff in HLU. destruct HLU as [HL HU].
    simpl. f_equal; [apply IHA1; auto | apply IHA2; auto |].
    apply functional_extensionality. intros A0.
    exact (IHA3 (A0 :: tvars1) tvars2 venv S1 S2 HB).
  - (* TRefine *)
    simpl. f_equal. apply IHA; auto.
  - (* TSigma *)
    apply andb_true_iff in Habsent. destruct Habsent as [HA HB].
    simpl. f_equal; [apply IHA1; auto |].
    apply functional_extensionality. intros v1. apply IHA2; auto.
  - (* TSum *)
    apply andb_true_iff in Habsent. destruct Habsent as [HA HB].
    simpl. f_equal; [apply IHA1 | apply IHA2]; auto.
  - (* TOr *)
    apply andb_true_iff in Habsent. destruct Habsent as [HA HB].
    simpl. f_equal; [apply IHA1 | apply IHA2]; auto.
  - (* TAnd *)
    apply andb_true_iff in Habsent. destruct Habsent as [HA HB].
    simpl. f_equal; [apply IHA1 | apply IHA2]; auto.
  - (* TMuAll *)
    simpl. apply functional_extensionality. intros v.
    apply propositional_extensionality.
    assert (Hext: forall X w,
      interp (X :: tvars1 ++ S1 :: tvars2) venv A w <->
      interp (X :: tvars1 ++ S2 :: tvars2) venv A w). {
      intros X w.
      enough (interp (X :: tvars1 ++ S1 :: tvars2) venv A =
              interp (X :: tvars1 ++ S2 :: tvars2) venv A) as -> by tauto.
      exact (IHA (X :: tvars1) tvars2 venv S1 S2 Habsent). }
    split; intros H n; specialize (H n).
    + exact (proj1 (interp_mu_eq_ext n _ _ Hext v) H).
    + exact (proj2 (interp_mu_eq_ext n _ _ Hext v) H).
Qed.

(** ** Monotonicity: positive types are covariant

    If type variable [i] is strictly positive in [A], and [S1 ⊆ S2],
    then [interp ... S1 ... A v → interp ... S2 ... A v]. *)

Lemma interp_spos_mono: forall A tvars1 tvars2 venv S1 S2 v,
  spos (length tvars1) A = true ->
  (forall w, S1 w -> S2 w) ->
  interp (tvars1 ++ S1 :: tvars2) venv A v ->
  interp (tvars1 ++ S2 :: tvars2) venv A v.
Proof.
  induction A; intros tvars1 tvars2 venv S1 S2 val Hspos Hmono Hinterp;
    simpl in Hspos; try exact Hinterp.
  - (* TVar *)
    simpl in *. unfold interp_var in *.
    destruct (lt_dec v (length tvars1)) as [Hlt | Hge].
    + rewrite nth_error_app1 in * by lia. exact Hinterp.
    + rewrite nth_error_app2 in * by lia.
      destruct (v - length tvars1) as [|k] eqn:Ek.
      * simpl in *. apply Hmono. exact Hinterp.
      * simpl in *. exact Hinterp.
  - (* TFun *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in Hinterp |- *. destruct Hinterp as [venv' [body [Hv Hfun]]].
    exists venv', body. split; [exact Hv |].
    intros arg Harg.
    pose proof (interp_ty_var_absent A1 tvars1 tvars2 venv S1 S2 HA) as HeqA1.
    assert (Harg': interp (tvars1 ++ S1 :: tvars2) venv A1 arg) by
      exact (transport_fun_rev _ _ arg HeqA1 Harg).
    eapply term_has_semtype_mono.
    2: exact (Hfun arg Harg').
    intros v'. apply (IHA2 tvars1 tvars2 (arg :: venv) S1 S2 v' HB Hmono).
  - (* TForall *)
    apply andb_true_iff in Hspos. destruct Hspos as [HLU HB].
    apply andb_true_iff in HLU. destruct HLU as [HL HU].
    simpl in Hinterp |- *. destruct Hinterp as [env [body [Hv Hsem]]].
    exists env, body. split; [exact Hv |].
    intros A0 HsubL HsubU.
    pose proof (interp_ty_var_absent A1 tvars1 tvars2 venv S1 S2 HL) as HeqL.
    pose proof (interp_ty_var_absent A2 tvars1 tvars2 venv S1 S2 HU) as HeqU.
    assert (HsubL': forall w, interp (tvars1 ++ S1 :: tvars2) venv A1 w -> A0 w). {
      intros w Hw. apply HsubL. exact (transport_fun _ _ w HeqL Hw). }
    assert (HsubU': forall w, A0 w -> interp (tvars1 ++ S1 :: tvars2) venv A2 w). {
      intros w Hw. exact (transport_fun_rev _ _ w HeqU (HsubU w Hw)). }
    eapply term_has_semtype_mono.
    2: exact (Hsem A0 HsubL' HsubU').
    intros v'. apply (IHA3 (A0 :: tvars1) tvars2 venv S1 S2 v' HB Hmono).
  - (* TRefine *)
    simpl in Hinterp |- *. destruct Hinterp as [HA' Hpred].
    split; [apply (IHA tvars1 tvars2 venv S1 S2 val Hspos Hmono HA') | exact Hpred].
  - (* TSigma *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in Hinterp |- *. destruct Hinterp as [v1 [v2 [Hv [H1 H2]]]].
    exists v1, v2. split; [exact Hv |]. split.
    + apply (IHA1 tvars1 tvars2 venv S1 S2 v1 HA Hmono H1).
    + apply (IHA2 tvars1 tvars2 (v1 :: venv) S1 S2 v2 HB Hmono H2).
  - (* TSum *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in Hinterp |- *. destruct Hinterp as [[w [Hv Hw]] | [w [Hv Hw]]].
    + left. exists w. split; [exact Hv |].
      apply (IHA1 tvars1 tvars2 venv S1 S2 w HA Hmono Hw).
    + right. exists w. split; [exact Hv |].
      apply (IHA2 tvars1 tvars2 venv S1 S2 w HB Hmono Hw).
  - (* TOr *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in Hinterp |- *. destruct Hinterp as [Hinterp | Hinterp].
    + left. exact (transport_fun _ _ val (interp_ty_var_absent A1 tvars1 tvars2 venv S1 S2 HA) Hinterp).
    + right. exact (transport_fun _ _ val (interp_ty_var_absent A2 tvars1 tvars2 venv S1 S2 HB) Hinterp).
  - (* TAnd *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in Hinterp |- *. destruct Hinterp as [H1 H2]. split.
    + apply (IHA1 tvars1 tvars2 venv S1 S2 val HA Hmono H1).
    + apply (IHA2 tvars1 tvars2 venv S1 S2 val HB Hmono H2).
  - (* TMuAll *)
    apply andb_true_iff in Hspos. destruct Hspos as [Hspos0 HabsI].
    simpl in Hinterp |- *.
    assert (Hext: forall X w,
      interp (X :: tvars1 ++ S1 :: tvars2) venv A w <->
      interp (X :: tvars1 ++ S2 :: tvars2) venv A w). {
      intros X w.
      enough (interp (X :: tvars1 ++ S1 :: tvars2) venv A =
              interp (X :: tvars1 ++ S2 :: tvars2) venv A) as -> by tauto.
      exact (interp_ty_var_absent A (X :: tvars1) tvars2 venv S1 S2 HabsI). }
    intros m.
    apply (proj1 (interp_mu_eq_ext m _ _ Hext val)).
    exact (Hinterp m).
Qed.

(** ** Distributing lemma: universal quantifier commutes with positive contexts

    If type variable [i] is strictly positive in [A], then:
    [(∀n. interp (Sn n :: ...) A v) → interp ((λw. ∀n. Sn n w) :: ...) A v]

    Key proof technique: structural induction on [A].
    - [TVar j] with [j = i]: hypothesis directly gives [∀n. Sn n v]
    - [TFun A B]: domain is constant (by [ty_var_absent]); for each arg,
      determinism of evaluation ensures the same result w for all n,
      then apply IH on B to collect [∀n. B[Sn n] w] → [B[∩S] w]
    - [TOr A B]: both branches are constant (by [ty_var_absent])
    - [TForall L U B], [TMuAll B]: index shifts, IH with extended [tvars1] *)

Lemma interp_spos_distribute: forall A tvars1 tvars2 venv (Sn: nat -> SemTy) v,
  spos (length tvars1) A = true ->
  (forall n, interp (tvars1 ++ Sn n :: tvars2) venv A v) ->
  interp (tvars1 ++ (fun w => forall n, Sn n w) :: tvars2) venv A v.
Proof.
  induction A; intros tvars1 tvars2 venv Sn val Hspos Hall;
    simpl in Hspos; try (exact (Hall 0)).
  - (* TVar *)
    simpl. unfold interp_var.
    destruct (lt_dec v (length tvars1)) as [Hlt | Hge].
    + rewrite nth_error_app1 by lia.
      pose proof (Hall 0) as H. simpl in H. unfold interp_var in H.
      rewrite nth_error_app1 in H by lia. exact H.
    + rewrite nth_error_app2 by lia.
      destruct (v - length tvars1) as [|k] eqn:Ek.
      * simpl. intros n.
        pose proof (Hall n) as H. simpl in H. unfold interp_var in H.
        rewrite nth_error_app2 in H by lia. rewrite Ek in H. simpl in H. exact H.
      * simpl.
        pose proof (Hall 0) as H. simpl in H. unfold interp_var in H.
        rewrite nth_error_app2 in H by lia. rewrite Ek in H. simpl in H. exact H.
  - (* TFun *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in *.
    destruct (Hall 0) as [venv' [body [Hv Hfun0]]].
    exists venv', body. split; [exact Hv |].
    intros arg Harg.
    pose proof (fun n => interp_ty_var_absent A1 tvars1 tvars2 venv (Sn n) (fun w => forall m, Sn m w) HA) as HeqA1.
    assert (Harg_n: forall n, interp (tvars1 ++ Sn n :: tvars2) venv A1 arg) by
      (intros n; exact (transport_fun_rev _ _ arg (HeqA1 n) Harg)).
    intros fuel r Heval.
    destruct (Hfun0 arg (Harg_n 0) fuel r Heval) as [w [Hr Hw0]].
    exists w. split; [exact Hr |].
    apply (IHA2 tvars1 tvars2 (arg :: venv) Sn w HB).
    intros n.
    destruct (Hall n) as [venv'n [bodyn [Hvn Hfunn]]].
    rewrite Hv in Hvn. injection Hvn as <- <-.
    destruct (Hfunn arg (Harg_n n) fuel r Heval) as [w' [Hr' Hw']].
    rewrite Hr in Hr'. injection Hr' as <-. exact Hw'.
  - (* TForall *)
    apply andb_true_iff in Hspos. destruct Hspos as [HLU HB].
    apply andb_true_iff in HLU. destruct HLU as [HL HU].
    simpl in *.
    destruct (Hall 0) as [env [body [Hv Hsem0]]].
    exists env, body. split; [exact Hv |].
    intros A0 HsubL HsubU.
    pose proof (fun n => interp_ty_var_absent A1 tvars1 tvars2 venv (Sn n) (fun w0 => forall m, Sn m w0) HL) as HeqL.
    pose proof (fun n => interp_ty_var_absent A2 tvars1 tvars2 venv (Sn n) (fun w0 => forall m, Sn m w0) HU) as HeqU.
    assert (HsubL_n: forall n, forall w, interp (tvars1 ++ Sn n :: tvars2) venv A1 w -> A0 w). {
      intros n w Hw. apply HsubL. exact (transport_fun _ _ w (HeqL n) Hw). }
    assert (HsubU_n: forall n, forall w, A0 w -> interp (tvars1 ++ Sn n :: tvars2) venv A2 w). {
      intros n w Hw. exact (transport_fun_rev _ _ w (HeqU n) (HsubU w Hw)). }
    assert (Hsem_n: forall n,
      term_has_semtype env body
        (interp (A0 :: tvars1 ++ Sn n :: tvars2) venv A3)). {
      intros n. destruct (Hall n) as [envn [bodyn [Hvn Hsemn]]].
      rewrite Hv in Hvn. injection Hvn as -> ->. apply Hsemn.
      exact (HsubL_n n). exact (HsubU_n n). }
    intros fuel r Heval.
    destruct (Hsem_n 0 fuel r Heval) as [w [Hr Hw0]].
    exists w. split; [exact Hr |].
    apply (IHA3 (A0 :: tvars1) tvars2 venv Sn w HB).
    intros n. destruct (Hsem_n n fuel r Heval) as [w' [Hr' Hw']].
    rewrite Hr in Hr'. injection Hr' as <-. exact Hw'.
  - (* TRefine *)
    simpl in *. split.
    + apply (IHA tvars1 tvars2 venv Sn val Hspos).
      intros n. exact (proj1 (Hall n)).
    + exact (proj2 (Hall 0)).
  - (* TSigma *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in *.
    destruct (Hall 0) as [v1 [v2 [Hv [H1_0 H2_0]]]].
    exists v1, v2. split; [exact Hv |]. split.
    + apply (IHA1 tvars1 tvars2 venv Sn v1 HA).
      intros n. destruct (Hall n) as [v1' [v2' [Hv' [H1' H2']]]].
      rewrite Hv in Hv'. injection Hv' as <- <-. exact H1'.
    + apply (IHA2 tvars1 tvars2 (v1 :: venv) Sn v2 HB).
      intros n. destruct (Hall n) as [v1' [v2' [Hv' [H1' H2']]]].
      rewrite Hv in Hv'. injection Hv' as <- <-. exact H2'.
  - (* TSum *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in *.
    destruct (Hall 0) as [[w [Hv Hw]] | [w [Hv Hw]]].
    + left. exists w. split; [exact Hv |].
      apply (IHA1 tvars1 tvars2 venv Sn w HA).
      intros n. destruct (Hall n) as [[w' [Hv' Hw']] | [w' [Hv' Hw']]].
      * rewrite Hv in Hv'. injection Hv' as <-. exact Hw'.
      * rewrite Hv in Hv'. discriminate.
    + right. exists w. split; [exact Hv |].
      apply (IHA2 tvars1 tvars2 venv Sn w HB).
      intros n. destruct (Hall n) as [[w' [Hv' Hw']] | [w' [Hv' Hw']]].
      * rewrite Hv in Hv'. discriminate.
      * rewrite Hv in Hv'. injection Hv' as <-. exact Hw'.
  - (* TOr *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in *.
    destruct (Hall 0) as [H | H].
    + left. exact (transport_fun _ _ val
        (interp_ty_var_absent A1 tvars1 tvars2 venv (Sn 0) _ HA) H).
    + right. exact (transport_fun _ _ val
        (interp_ty_var_absent A2 tvars1 tvars2 venv (Sn 0) _ HB) H).
  - (* TAnd *)
    apply andb_true_iff in Hspos. destruct Hspos as [HA HB].
    simpl in *. split.
    + apply (IHA1 tvars1 tvars2 venv Sn val HA).
      intros n. exact (proj1 (Hall n)).
    + apply (IHA2 tvars1 tvars2 venv Sn val HB).
      intros n. exact (proj2 (Hall n)).
  - (* TMuAll *)
    apply andb_true_iff in Hspos. destruct Hspos as [Hspos0 HabsI].
    simpl in *.
    assert (Hext: forall X w,
      interp (X :: tvars1 ++ Sn 0 :: tvars2) venv A w <->
      interp (X :: tvars1 ++ (fun w0 => forall n0, Sn n0 w0) :: tvars2) venv A w). {
      intros X w.
      enough (interp (X :: tvars1 ++ Sn 0 :: tvars2) venv A =
              interp (X :: tvars1 ++ (fun w0 => forall n0, Sn n0 w0) :: tvars2) venv A)
        as -> by tauto.
      exact (interp_ty_var_absent A (X :: tvars1) tvars2 venv (Sn 0) _ HabsI). }
    intros m.
    apply (proj1 (interp_mu_eq_ext m _ _ Hext val)).
    exact (Hall 0 m).
Qed.

(** ** Monotonicity of interp_mu in F

    If [F1 X ⊆ F2 X] pointwise and [F2] is monotone, then
    [interp_mu n F1 v → interp_mu n F2 v]. *)

Lemma interp_mu_mono: forall n (F1 F2 : SemTy -> SemTy),
  (forall X v, F1 X v -> F2 X v) ->
  (forall S1 S2, (forall w, S1 w -> S2 w) -> forall w, F2 S1 w -> F2 S2 w) ->
  forall v, interp_mu n F1 v -> interp_mu n F2 v.
Proof.
  induction n; intros F1 F2 Hpw Fmono v Hmu.
  - simpl in *. trivial.
  - simpl in *. eapply Fmono.
    + intros u Hu. exact (IHn F1 F2 Hpw Fmono u Hu).
    + eapply Hpw. exact Hmu.
Qed.
