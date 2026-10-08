(** * Well-Formedness Lemmas

    Extension, lookup, and shifting lemmas for the three well-formedness
    predicates of [Wf]: [wf_env], [wf_benv], and [wf_facts]. *)


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
Require Import RefinementTypes.InterpLemmas.
Require Import RefinementTypes.Wf.

(** ** Lemmas about wf_env *)

Lemma wf_env_length: forall tvars tenv venv,
  wf_env tvars tenv venv -> length tenv = length venv.
Proof.
  intros tvars tenv. revert tvars.
  induction tenv as [| T tenv' IH]; intros tvars venv Hwf.
  - destruct venv; [reflexivity|simpl in Hwf; contradiction].
  - destruct venv as [| v venv']; [simpl in Hwf; contradiction|].
    simpl in Hwf. destruct Hwf as [Hinterp Hwf'].
    simpl. f_equal. eapply IH. exact Hwf'.
Qed.

Lemma wf_env_lookup: forall tvars tenv venv i T,
  wf_env tvars tenv venv ->
  nth_error tenv i = Some T ->
  exists v,
    nth_error venv i = Some v /\
    interp tvars (skipn (S i) venv) T v.
Proof.
  intros tvars tenv. revert tvars.
  induction tenv as [| T0 tenv' IH]; intros tvars venv i T Hwf Hnth.
  - destruct i; discriminate.
  - destruct venv as [| v0 venv']; [simpl in Hwf; contradiction |].
    simpl in Hwf. destruct Hwf as [Hinterp Hwf'].
    destruct i as [| i'].
    + simpl in Hnth. injection Hnth as ->. exists v0. simpl. auto.
    + simpl. eapply IH; eauto.
Qed.

Lemma env_incr_wf: forall tvars tenv venv T',
  wf_env tvars tenv venv -> wf_env (T'::tvars) (tenv_shift_type tenv) venv.
Proof.
  intros tvars tenv. revert tvars.
  induction tenv as [| T tenv' IH]; intros tvars [| v venv'] T' Hwf;
    simpl in *; try contradiction; auto.
  destruct Hwf as [Hinterp Hwf'].
  split.
  - rewrite <- interp_env_ren_type. exact Hinterp.
  - apply IH. exact Hwf'.
Qed.

(** ** Lemmas about wf_facts *)

Lemma skipn_extend: forall (venv: list Value) (v: Value) d,
  d <= length venv ->
  skipn (length (v :: venv) - d) (v :: venv) = skipn (length venv - d) venv.
Proof.
  intros venv v d Hle.
  simpl length. simpl Nat.sub.
  destruct d as [| d'].
  - rewrite Nat.sub_0_r. simpl. reflexivity.
  - replace (length venv - d') with (S (length venv - S d')) by lia.
    simpl. reflexivity.
Qed.

Lemma wf_facts_extend: forall venv v facts,
  wf_facts venv facts -> wf_facts (v :: venv) facts.
Proof.
  intros venv v facts Hfacts. unfold wf_facts in *.
  induction facts as [| [[d1 t1] [d2 t2]] facts' IH]; [constructor |].
  inversion Hfacts; subst. constructor; [| auto].
  destruct H1 as [Hle1 [Hle2 Heval]].
  split; [simpl; lia |].
  split; [simpl; lia |].
  rewrite !skipn_extend by lia. exact Heval.
Qed.

(** ** Lemmas about wf_benv *)

Lemma wf_benv_shift_term: forall tvars tbounds venv val,
  wf_benv tvars tbounds venv ->
  wf_benv tvars (tbounds_shift_term tbounds) (val :: venv).
Proof.
  intros tvars. induction tvars as [| A tvars' IH];
    intros tbounds venv val Hwf.
  - destruct tbounds; [exact I | contradiction].
  - destruct tbounds as [| [L U] tbounds']; [contradiction |].
    simpl in Hwf. destruct Hwf as [HL [HU Hwf']].
    change (tbounds_shift_term ((L, U) :: tbounds'))
      with ((ren_ty id S L, ren_ty id S U) :: tbounds_shift_term tbounds').
    simpl wf_benv. repeat split.
    + intros w Hw. apply HL.
      rewrite <- (interp_env_ren_term L tvars' venv val) in Hw. exact Hw.
    + intros w Hw.
      rewrite <- (interp_env_ren_term U tvars' venv val).
      apply HU. exact Hw.
    + apply IH. exact Hwf'.
Qed.

Lemma wf_benv_lookup: forall tvars tbounds venv i L U,
  wf_benv tvars tbounds venv ->
  nth_error tbounds i = Some (L, U) ->
  exists A,
    nth_error tvars i = Some A /\
    (forall w, interp (skipn (S i) tvars) venv L w -> A w) /\
    (forall w, A w -> interp (skipn (S i) tvars) venv U w).
Proof.
  intros tvars. induction tvars as [| A tvars' IH];
    intros tbounds venv i L U Hwf Hnth.
  - destruct tbounds; [destruct i; discriminate | contradiction].
  - destruct tbounds as [| [L0 U0] tbounds']; [contradiction |].
    simpl in Hwf. destruct Hwf as [HL0 [HU0 Hwf']].
    destruct i as [| i'].
    + simpl in Hnth. injection Hnth as -> ->. exists A. simpl. auto.
    + simpl in Hnth. simpl. apply (IH tbounds' venv i' L U Hwf' Hnth).
Qed.

(** Shifting type variables by [k] in interpretation corresponds to
    dropping the first [k] entries from [tvars]. *)
Lemma interp_shift_type_by: forall T tvars venv k,
  k <= length tvars ->
  interp (skipn k tvars) venv T =
  interp tvars venv (ren_ty (fun n => n + k) id T).
Proof.
  intros T tvars venv k Hle.
  rewrite <- (firstn_skipn k tvars) at 2.
  change (firstn k tvars ++ skipn k tvars)
    with ([] ++ firstn k tvars ++ skipn k tvars).
  change (skipn k tvars) with ([] ++ skipn k tvars) at 1.
  rewrite (interp_weaken_type T [] (firstn k tvars) (skipn k tvars) venv).
  f_equal. apply ren_ty_ext.
  - intro n. simpl. rewrite firstn_length_le; lia.
  - reflexivity.
Qed.

Lemma wf_facts_cons: forall venv d1 t1 d2 t2 facts,
  d1 <= length venv ->
  d2 <= length venv ->
  evals_to_same (skipn (length venv - d1) venv) t1
                (skipn (length venv - d2) venv) t2 ->
  wf_facts venv facts ->
  wf_facts venv (((d1, t1), (d2, t2)) :: facts).
Proof.
  intros venv d1 t1 d2 t2 facts Hle1 Hle2 Heval Hfacts.
  unfold wf_facts in *. constructor; [| exact Hfacts].
  repeat split; assumption.
Qed.

(** ** Lemmas about wf_ctx *)

Lemma wf_ctx_length: forall tvars gamma venv,
  wf_ctx tvars gamma venv -> ctx_len gamma = length venv.
Proof. intros tvars gamma venv [Henv _]. apply (wf_env_length tvars). exact Henv. Qed.

Lemma wf_ctx_lookup_term: forall tvars gamma venv i T,
  wf_ctx tvars gamma venv ->
  nth_error (ctx_tenv gamma) i = Some T ->
  exists v, nth_error venv i = Some v /\ interp tvars (skipn (S i) venv) T v.
Proof. intros tvars gamma venv i T [Henv _] Hnth. exact (wf_env_lookup _ _ _ _ _ Henv Hnth). Qed.

Lemma wf_ctx_lookup_type: forall tvars gamma venv i L U,
  wf_ctx tvars gamma venv ->
  nth_error (ctx_tbounds gamma) i = Some (L, U) ->
  exists X,
    nth_error tvars i = Some X /\
    (forall w, interp (skipn (S i) tvars) venv L w -> X w) /\
    (forall w, X w -> interp (skipn (S i) tvars) venv U w).
Proof. intros tvars gamma venv i L U [_ [Hbenv _]] Hnth. exact (wf_benv_lookup _ _ _ _ _ _ Hbenv Hnth). Qed.

(** Γ, x : A *)
Lemma wf_ctx_cons_term: forall tvars gamma venv A v,
  interp tvars venv A v ->
  wf_ctx tvars gamma venv ->
  wf_ctx tvars (ctx_cons_term gamma A) (v :: venv).
Proof.
  intros tvars gamma venv A v Hv [Henv [Hbenv Hfacts]]. split; [|split]; simpl.
  - exact (conj Hv Henv).
  - apply wf_benv_shift_term. exact Hbenv.
  - apply wf_facts_extend. exact Hfacts.
Qed.

(** Γ, X :> L <: U *)
Lemma wf_ctx_cons_type: forall tvars gamma venv L U X,
  (forall w, interp tvars venv L w -> X w) ->
  (forall w, X w -> interp tvars venv U w) ->
  wf_ctx tvars gamma venv ->
  wf_ctx (X :: tvars) (ctx_cons_type gamma L U) venv.
Proof.
  intros tvars gamma venv L U X HL HU [Henv [Hbenv Hfacts]]. split; [|split]; simpl.
  - apply env_incr_wf. exact Henv.
  - exact (conj HL (conj HU Hbenv)).
  - exact Hfacts.
Qed.

(** The equality facts recorded by the typing rules. For [if]: the
    condition equals the taken branch's boolean. *)
Lemma wf_ctx_fact_if: forall tvars gamma venv c b fuel,
  wf_ctx tvars gamma venv ->
  eval fuel venv c = Some (Some (vbool b)) ->
  wf_ctx tvars (ctx_add_fact gamma ((ctx_len gamma, c), (ctx_len gamma, tbool b))) venv.
Proof.
  intros tvars gamma venv c b fuel Hwf Heval.
  pose proof (wf_ctx_length _ _ _ Hwf) as Hlen. unfold ctx_len in *.
  destruct Hwf as [Henv [Hbenv Hfacts]]. split; [|split]; simpl; [exact Henv | exact Hbenv |].
  apply wf_facts_cons; [lia | lia | | exact Hfacts].
  rewrite Hlen, Nat.sub_diag. simpl.
  exists (vbool b), fuel, 1. split; [exact Heval | reflexivity].
Qed.

(** For [let]: the bound variable equals its definition. *)
Lemma wf_ctx_fact_let: forall tvars gamma venv A e v fuel,
  wf_ctx tvars gamma venv ->
  interp tvars venv A v ->
  eval fuel venv e = Some (Some v) ->
  wf_ctx tvars (ctx_add_fact (ctx_cons_term gamma A) ((S (ctx_len gamma), tvar 0), (ctx_len gamma, e)))
    (v :: venv).
Proof.
  intros tvars gamma venv A e v fuel Hwf Hv Heval.
  pose proof (wf_ctx_length _ _ _ Hwf) as Hlen. unfold ctx_len in *.
  destruct (wf_ctx_cons_term _ _ _ _ _ Hv Hwf) as [Henv' [Hbenv' Hfacts']].
  split; [|split]; simpl; [exact Henv' | exact Hbenv' |].
  apply wf_facts_cons; [simpl; lia | simpl; lia | | exact Hfacts'].
  change (length (v :: venv)) with (S (length venv)). rewrite Hlen, Nat.sub_diag.
  replace (S (length venv) - length venv) with 1 by lia. simpl.
  exists v, 1, fuel. split; [reflexivity | exact Heval].
Qed.

(** For [match]: the scrutinee equals the matched pattern, a term over the
    newly bound variable. *)
Lemma wf_ctx_fact_match: forall tvars gamma venv A e t u w fuel fuel',
  wf_ctx tvars gamma venv ->
  interp tvars venv A w ->
  eval fuel venv e = Some (Some u) ->
  eval fuel' (w :: venv) t = Some (Some u) ->
  wf_ctx tvars (ctx_add_fact (ctx_cons_term gamma A) ((ctx_len gamma, e), (S (ctx_len gamma), t)))
    (w :: venv).
Proof.
  intros tvars gamma venv A e t u w fuel fuel' Hwf Hw Heval Heval'.
  pose proof (wf_ctx_length _ _ _ Hwf) as Hlen. unfold ctx_len in *.
  destruct (wf_ctx_cons_term _ _ _ _ _ Hw Hwf) as [Henv' [Hbenv' Hfacts']].
  split; [|split]; simpl; [exact Henv' | exact Hbenv' |].
  apply wf_facts_cons; [simpl; lia | simpl; lia | | exact Hfacts'].
  change (length (w :: venv)) with (S (length venv)). rewrite Hlen.
  replace (S (length venv) - length venv) with 1 by lia. rewrite Nat.sub_diag. simpl.
  exists u, fuel, fuel'. split; [exact Heval | exact Heval'].
Qed.
