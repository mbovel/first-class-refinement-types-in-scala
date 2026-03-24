(** * Semantic Typing

    This file defines the semantic typing judgment and proves the fundamental
    lemmas for each syntactic construct. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Psatz.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.ListLemmas.
Require Import RefinementTypes.EvalLemmas.
Require Import RefinementTypes.EvalShiftLemmas.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.InterpShiftLemmas.
Require Import RefinementTypes.InterpSubstLemmas.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.WfLemmas.
Require Import RefinementTypes.Avoid.
Require Import RefinementTypes.AvoidLemmas.
Require Import RefinementTypes.FirstOrder.
Require Import RefinementTypes.FirstOrderLemmas.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.PositivityLemmas.
Require Import RefinementTypes.SemanticSubtyping.

(** Semantic typing: a term [t] has type [T] if, in any well-formed
    environment, evaluating [t] produces a value in the interpretation of [T]. *)
Definition sem_typed (tbounds: TBounds) (tenv: list Ty) (facts: list ((nat * Term) * (nat * Term))) (t: Term) (T: Ty) : Prop :=
  forall tvars venv,
    wf_env tvars tenv venv ->
    wf_benv tvars tbounds venv ->
    wf_facts venv facts ->
    term_has_semtype venv t (interp tvars venv T).

Lemma sem_typed_diverge: forall tbounds tenv facts T, sem_typed tbounds tenv facts tdiverge T.
Proof.
  intros tbounds tenv facts T tvars venv Henv Hbenv Hfacts fuel r Heval.
  destruct fuel; discriminate.
Qed.

Lemma sem_typed_unit: forall tbounds tenv facts, sem_typed tbounds tenv facts tunit TUnit.
Proof.
  intros tbounds tenv facts tvars venv Henv Hbenv Hfacts fuel r Heval.
  destruct fuel; [discriminate|].
  simpl in Heval. injection Heval as <-.
  exists vunit. simpl. auto.
Qed.

Lemma sem_typed_bool: forall tbounds tenv facts b, sem_typed tbounds tenv facts (tbool b) TBool.
Proof.
  intros tbounds tenv facts b tvars venv Henv Hbenv Hfacts.
  intros fuel r Heval.
  destruct fuel; [discriminate|].
  simpl in Heval. injection Heval as <-.
  exists (vbool b). simpl. split; [reflexivity|]. exists b. reflexivity.
Qed.

Lemma sem_typed_int32: forall tbounds tenv facts z, sem_typed tbounds tenv facts (tint32 z) TInt32.
Proof.
  intros tbounds tenv facts z tvars venv Henv Hbenv Hfacts.
  intros fuel r Heval.
  destruct fuel; [discriminate|].
  simpl in Heval. injection Heval as <-.
  exists (vint32 z). simpl. split; [reflexivity|]. exists z. reflexivity.
Qed.

Lemma sem_typed_var: forall tbounds tenv facts i T,
  nth_error tenv i = Some T ->
  sem_typed tbounds tenv facts (tvar i) (subst_ty TVar (tm_shift (S i)) T).
Proof.
  intros tbounds tenv facts i T Hnth tvars venv Henv Hbenv Hfacts.
  destruct (wf_env_lookup tvars tenv venv i T Henv Hnth) as [v [Hvnth Hinterp]].
  intros fuel r Heval.
  destruct fuel; [discriminate|].
  simpl in Heval. rewrite Hvnth in Heval. injection Heval as <-.
  exists v. split; [reflexivity|].
  assert (Hle: S i <= length venv).
  { assert (i < length venv) by (apply nth_error_Some; rewrite Hvnth; discriminate). lia. }
  pose proof (interp_weaken_term T tvars [] (firstn (S i) venv) (skipn (S i) venv)) as Heq.
  rewrite firstn_skipn in Heq.
  rewrite firstn_length_le in Heq; [| lia].
  change ([] ++ ?x) with x in Heq.
  change (length (@nil Value)) with 0 in Heq.
  change (upn_tm 0 ?sigma) with sigma in Heq.
  rewrite <- Heq. exact Hinterp.
Qed.

Lemma sem_typed_abs: forall tbounds tenv facts A b B,
  sem_typed (tbounds_shift_term tbounds) (A :: tenv) facts b B ->
  sem_typed tbounds tenv facts (tabs A b) (TFun A B).
Proof.
  intros tbounds tenv facts A b B Hbody tvars venv Henv Hbenv Hfacts.
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval. injection Heval as <-.
  exists (vabs venv b). split; [reflexivity|].
  simpl. unfold interp_fun.
  exists venv, b. split; [reflexivity|].
  intros arg Harg.
  apply (Hbody tvars (arg :: venv)).
  - apply wf_env_cons; assumption.
  - apply wf_benv_shift_term. exact Hbenv.
  - apply wf_facts_extend. exact Hfacts.
Qed.

Lemma sem_typed_app_anf: forall tbounds tenv facts fn i A B,
  sem_typed tbounds tenv facts fn (TFun A B) ->
  sem_typed tbounds tenv facts (tvar i) A ->
  sem_typed tbounds tenv facts (tapp fn (tvar i)) (subst_ty TVar (tvar i .: tvar) B).
Proof.
  intros tbounds tenv facts fn i A B Hfn Ha tvars venv Henv Hbenv Hfacts.
  specialize (Hfn tvars venv Henv Hbenv Hfacts).
  specialize (Ha tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv fn) as [[vf|]|] eqn:Hevalfn.
  - destruct (Hfn _ _ Hevalfn) as [vf' [Hvf' Hinterpf]].
    injection Hvf' as <-.
    destruct Hinterpf as [envf [body [Heqf Hbody]]].
    subst vf.
    destruct (eval fuel' venv (tvar i)) as [[va|]|] eqn:Hevala.
    + destruct (Ha _ _ Hevala) as [va' [Hva' Hinterpa]].
      injection Hva' as <-.
      specialize (Hbody va Hinterpa).
      destruct (Hbody _ _ Heval) as [v [Hv Hvb]].
      exists v. split; [exact Hv|].
      assert (Hnth: nth_error venv i = Some va).
      { destruct fuel'; [discriminate Hevala|].
        simpl in Hevala. destruct (nth_error venv i); congruence. }
      rewrite <- interp_subst_term with (va := va); auto.
    + destruct (Ha _ _ Hevala) as [? [Habs _]]; discriminate.
    + discriminate.
  - destruct (Hfn _ _ Hevalfn) as [? [Habs _]]; discriminate.
  - discriminate.
Qed.

Lemma sem_typed_tabs: forall tbounds tenv facts L U b A,
  sem_typed ((L, U) :: tbounds) (tenv_shift_type tenv) facts b A ->
  sem_typed tbounds tenv facts (ttabs L U b) (TForall L U A).
Proof.
  intros * Hbody tvars venv Henv Hbenv Hfacts.
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval. injection Heval as <-.
  exists (vtabs venv b). split; [reflexivity|].
  simpl. unfold interp_forall.
  exists venv, b. split; [reflexivity|].
  intros A' HL HU.
  apply (Hbody (A' :: tvars) venv).
  - apply env_incr_wf. exact Henv.
  - apply wf_benv_cons; assumption.
  - exact Hfacts.
Qed.

(** Type application uses semantic substitution. *)
Lemma sem_typed_tapp: forall tbounds tenv facts fn L U A B,
  sem_typed tbounds tenv facts fn (TForall L U B) ->
  sem_subtype tbounds tenv facts L A ->
  sem_subtype tbounds tenv facts A U ->
  sem_typed tbounds tenv facts (ttapp fn A) (ty_subst B A).
Proof.
  intros * Hfn HsubL HsubU tvars venv Henv Hbenv Hfacts.
  specialize (Hfn tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv fn) as [[vf|]|] eqn:Hevalfn; try discriminate.
  - destruct (Hfn _ _ Hevalfn) as [vf' [Hvf' Hinterpf]].
    injection Hvf' as <-.
    simpl in Hinterpf. unfold interp_forall in Hinterpf.
    destruct Hinterpf as [envf [body [Heqf Hbody]]].
    subst vf.
    specialize (Hbody (interp tvars venv A)).
    assert (HL': forall w, interp tvars venv L w -> interp tvars venv A w).
    { intros w Hw. exact (HsubL tvars venv Henv Hbenv Hfacts w Hw). }
    assert (HU': forall w, interp tvars venv A w -> interp tvars venv U w).
    { intros w Hw. exact (HsubU tvars venv Henv Hbenv Hfacts w Hw). }
    specialize (Hbody HL' HU').
    rewrite <- interp_subst.
    exact (Hbody _ _ Heval).
  - destruct (Hfn _ _ Hevalfn) as [? [Habs _]]; discriminate.
Qed.

(** Let binding with equality witness. *)
Lemma sem_typed_let: forall tbounds tenv facts e A b B z,
  sem_typed tbounds tenv facts e A ->
  sem_typed (tbounds_shift_term tbounds) (A :: tenv)
            (((S (length tenv), tvar 0), (length tenv, e)) :: facts) b B ->
  sem_typed tbounds tenv facts (tlet A e b)
    (subst_ty TVar (z .: tvar) (avoid_var0 B)).
Proof.
  intros * He Hb tvars venv Henv Hbenv Hfacts.
  specialize (He tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv e) as [[ve|]|] eqn:Hevale; try discriminate.
  - destruct (He _ _ Hevale) as [ve' [Hve' Hinterpe]].
    injection Hve' as <-.
    (* Build wf_env and wf_facts for the extended environment *)
    assert (Henv': wf_env tvars (A :: tenv) (ve :: venv)).
    { apply wf_env_cons; assumption. }
    assert (Hbenv': wf_benv tvars (tbounds_shift_term tbounds) (ve :: venv)).
    { apply wf_benv_shift_term. exact Hbenv. }
    assert (Hfacts': wf_facts (ve :: venv)
              (((S (length tenv), tvar 0), (length tenv, e)) :: facts)).
    { apply wf_facts_cons.
      - apply wf_env_length in Henv. simpl. lia.
      - apply wf_env_length in Henv. simpl. lia.
      - apply wf_env_length in Henv as Hlen.
        change (length (ve :: venv)) with (S (length venv)).
        rewrite Hlen, Nat.sub_diag.
        assert (Hsub: S (length venv) - length venv = 1).
        { rewrite Nat.sub_succ_l by auto. rewrite Nat.sub_diag. reflexivity. }
        rewrite Hsub. simpl.
        exists ve, 1, fuel'.
        split; [reflexivity | exact Hevale].
      - apply wf_facts_extend. exact Hfacts. }
    specialize (Hb tvars (ve :: venv) Henv' Hbenv' Hfacts').
    destruct (Hb _ _ Heval) as [v [Hv Hinterpv]].
    exists v. split; [exact Hv|].
    apply interp_avoid_var0 in Hinterpv.
    rewrite (interp_env_shift_term (subst_ty TVar (z .: tvar) (avoid_var0 B)) tvars venv ve).
    replace (ren_ty id S (subst_ty TVar (z .: tvar) (avoid_var0 B)))
      with (avoid_var0 B).
    2: { rewrite ren_subst_ty.
         transitivity (subst_ty TVar (fun n => tvar (S n))
                         (subst_ty TVar (z .: tvar) (avoid_var0 B))).
         - symmetry. exact (avoid_subst_shift_id B z).
         - apply subst_ty_ext; intro n; unfold funcomp; reflexivity. }
    exact Hinterpv.
  - destruct (He _ _ Hevale) as [? [Habs _]]; discriminate.
Qed.

(** Binary operations. *)
Lemma sem_typed_bin_op: forall tbounds tenv facts op a b T,
  sem_typed tbounds tenv facts a T ->
  sem_typed tbounds tenv facts b T ->
  bin_op_ty_compat op T = true ->
  sem_typed tbounds tenv facts (tbin_op op a b) (bin_op_result_ty op T).
Proof.
  intros * Ha Hb Hcompat tvars venv Henv Hbenv Hfacts.
  specialize (Ha tvars venv Henv Hbenv Hfacts).
  specialize (Hb tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv a) as [[va|]|] eqn:Hevala; try discriminate.
  - destruct (Ha _ _ Hevala) as [va' [Hva' Hinterpa]].
    injection Hva' as <-.
    destruct (eval fuel' venv b) as [[vb|]|] eqn:Hevalb; try discriminate.
    + destruct (Hb _ _ Hevalb) as [vb' [Hvb' Hinterpb]].
      injection Hvb' as <-.
      pose proof (bin_op_ty_interp_val_pair_compat op T tvars venv va vb Hcompat Hinterpa Hinterpb) as Hvalcompat.
      pose proof (eval_bin_op_defined op va vb Hvalcompat) as [v Hop].
      rewrite Hop in Heval. injection Heval as <-.
      exists v. split; [reflexivity|].
      exact (eval_bin_op_result_in_interp op T tvars venv va vb v Hcompat Hinterpa Hinterpb Hop).
    + destruct (Hb _ _ Hevalb) as [? [Habs _]]; discriminate.
  - destruct (Ha _ _ Hevala) as [? [Habs _]]; discriminate.
Qed.

(** If-then-else. *)
Lemma sem_typed_if: forall tbounds tenv facts c t e T1 T2,
  sem_typed tbounds tenv facts c TBool ->
  sem_typed tbounds tenv (((length tenv, c), (length tenv, tbool true)) :: facts) t T1 ->
  sem_typed tbounds tenv (((length tenv, c), (length tenv, tbool false)) :: facts) e T2 ->
  sem_typed tbounds tenv facts (tif c t e) (TOr T1 T2).
Proof.
  intros * Hc Ht He tvars venv Henv Hbenv Hfacts.
  specialize (Hc tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv c) as [[vc|]|] eqn:Hevalc; try discriminate.
  - destruct (Hc _ _ Hevalc) as [vc' [Hvc' Hinterpc]].
    injection Hvc' as <-.
    simpl in Hinterpc. destruct Hinterpc as [bc Hbc]. subst vc.
    destruct bc.
    + (* true branch *)
      assert (Hfacts': wf_facts venv (((length tenv, c), (length tenv, tbool true)) :: facts)).
      { apply wf_facts_cons.
        - apply wf_env_length in Henv as Hlen. lia.
        - apply wf_env_length in Henv as Hlen. lia.
        - apply wf_env_length in Henv as Hlen.
          rewrite Hlen, Nat.sub_diag. simpl.
          exists (vbool true), fuel', 1. split; [assumption | reflexivity].
        - exact Hfacts. }
      specialize (Ht tvars venv Henv Hbenv Hfacts').
      destruct (Ht _ _ Heval) as [v [Hv Hinterpv]].
      exists v. split; [exact Hv|].
      simpl. unfold interp_or. left. exact Hinterpv.
    + (* false branch *)
      assert (Hfacts': wf_facts venv (((length tenv, c), (length tenv, tbool false)) :: facts)).
      { apply wf_facts_cons.
        - apply wf_env_length in Henv as Hlen. lia.
        - apply wf_env_length in Henv as Hlen. lia.
        - apply wf_env_length in Henv as Hlen.
          rewrite Hlen, Nat.sub_diag. simpl.
          exists (vbool false), fuel', 1. split; [assumption | reflexivity].
        - exact Hfacts. }
      specialize (He tvars venv Henv Hbenv Hfacts').
      destruct (He _ _ Heval) as [v [Hv Hinterpv]].
      exists v. split; [exact Hv|].
      simpl. unfold interp_or. right. exact Hinterpv.
  - destruct (Hc _ _ Hevalc) as [? [Habs _]]; discriminate.
Qed.

(** Loop. The conditions [HclA] and [HclB] require that [A] and [B] have no free
    term variables, so that [interp] is invariant under environment extension. *)
Lemma sem_typed_loop: forall tbounds tenv facts a A body B,
  ren_ty id S A = A ->
  ren_ty id S B = B ->
  sem_typed tbounds tenv facts a A ->
  sem_typed (tbounds_shift_term tbounds) (A :: tenv) facts body (TSum A B) ->
  sem_typed tbounds tenv facts (tloop a body) B.
Proof.
  intros * HclA HclB Ha Hbody tvars venv Henv Hbenv Hfacts.
  specialize (Ha tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv a) as [[va|]|] eqn:Hevala; try discriminate.
  2: { destruct (Ha _ _ Hevala) as [? [Habs _]]; discriminate. }
  destruct (Ha _ _ Hevala) as [va' [Hva' Hinterpa]].
  injection Hva' as <-.
  eapply run_loop_typed; [exact Hinterpa | | exact Heval].
  intros v HAv r0 Hr0.
  assert (Henv': wf_env tvars (A :: tenv) (v :: venv))
    by (apply wf_env_cons; assumption).
  assert (Hbenv': wf_benv tvars (tbounds_shift_term tbounds) (v :: venv))
    by (apply wf_benv_shift_term; exact Hbenv).
  assert (Hfacts': wf_facts (v :: venv) facts)
    by (apply wf_facts_extend; exact Hfacts).
  specialize (Hbody tvars (v :: venv) Henv' Hbenv' Hfacts').
  destruct (Hbody _ _ Hr0) as [w [Hw Hinterpw]].
  exists w. split; [exact Hw|].
  simpl in Hinterpw.
  assert (Hinterp_eq_A: interp tvars (v :: venv) A = interp tvars venv A).
  { rewrite (interp_env_shift_term A tvars venv v). rewrite HclA. reflexivity. }
  assert (Hinterp_eq_B: interp tvars (v :: venv) B = interp tvars venv B).
  { rewrite (interp_env_shift_term B tvars venv v). rewrite HclB. reflexivity. }
  destruct Hinterpw as [[u [Heq HA]] | [u [Heq HB]]].
  - (* vinl u - continue *) subst w. rewrite Hinterp_eq_A in HA. exact HA.
  - (* vinr u - break *) subst w. rewrite Hinterp_eq_B in HB. exact HB.
Qed.

(** Selfification: if e has first-order type T, then e also has the
    singleton type {x: T | x = e}. *)
Lemma sem_typed_selfify: forall tbounds tenv facts e T,
  sem_typed tbounds tenv facts e T ->
  fo T = true ->
  sem_typed tbounds tenv facts e (TRefine T (tbin_op OpEq (tvar 0) (ren_tm id S e))).
Proof.
  intros * Htyped Hfo tvars venv Henv Hbenv Hfacts.
  specialize (Htyped tvars venv Henv Hbenv Hfacts).
  unfold term_has_semtype in *.
  intros fuel r Heval.
  destruct (Htyped fuel r Heval) as [v [Hv Hinterp]].
  subst r. exists v. split; [reflexivity|].
  simpl. unfold interp_refine. split; [exact Hinterp|].
  pose proof (fo_interp_is_fo_val T tvars venv v Hfo Hinterp) as Hfov.
  (* Construct evaluation: tbin_op OpEq (tvar 0) (ren_tm id S e) in (v :: venv) *)
  (* Step 1: tvar 0 evaluates to v in 1 step *)
  assert (Heval_var: eval 1 (v :: venv) (tvar 0) = Some (Some v)).
  { reflexivity. }
  (* Step 2: ren_tm id S e evaluates to v' with val_weaken_compat v v' *)
  assert (Hren_eq: ren_tm id S e = subst_tm TVar (tm_shift 1) e).
  { rewrite ren_subst_tm. apply subst_tm_ext.
    - intro n. reflexivity.
    - intro n. unfold funcomp, tm_shift. f_equal. lia. }
  pose proof (eval_shift_env_fwd fuel e [] [v] venv _ Heval) as [r' [Hrc Hr']].
  simpl in Hr'.
  (* r' is compatible with Some (Some v) *)
  assert (Hr'_eq: r' = Some (Some v)).
  { inversion Hrc; subst.
    f_equal. f_equal.
    destruct Hfov as [-> | [[b ->] | [z ->]]];
      inversion H0; subst; reflexivity. }
  subst r'. rewrite <- Hren_eq in Hr'_eq.
  (* Step 3: eval_bin_op OpEq v v = Some (vbool true) *)
  pose proof (eval_bin_op_eq_refl v Hfov) as Hop.
  (* Combine: eval (S (1 + fuel)) (v :: venv) (tbin_op ...) = Some (Some (vbool true)) *)
  pose proof (eval_tbin_op 1 fuel (v :: venv) OpEq (tvar 0) (ren_tm id S e)
    v v (vbool true) Heval_var Hr'_eq Hop) as Heval_binop.
  (* Now show eval_to_true *)
  unfold eval_to_true, term_has_semtype.
  intros fuel2 r2 Heval2.
  (* By determinism: any successful evaluation gives the same result *)
  destruct (Nat.le_ge_cases fuel2 (S (1 + fuel))) as [Hle | Hge].
  + apply (eval_fuel_mono _ _ _ _ _ Hle) in Heval2.
    rewrite Heval_binop in Heval2. injection Heval2 as <-.
    exists (vbool true). auto.
  + apply (eval_fuel_mono _ _ _ _ _ Hge) in Heval_binop.
    rewrite Heval_binop in Heval2. injection Heval2 as <-.
    exists (vbool true). auto.
Qed.

Lemma sem_typed_sub: forall tbounds tenv facts t A B,
  sem_typed tbounds tenv facts t A ->
  sem_subtype tbounds tenv facts A B ->
  sem_typed tbounds tenv facts t B.
Proof.
  intros * Htyped Hsub tvars venv Henv Hbenv Hfacts.
  specialize (Htyped tvars venv Henv Hbenv Hfacts).
  unfold term_has_semtype in *.
  intros fuel r Heval.
  destruct (Htyped fuel r Heval) as [v [Hv Hinterp]].
  exists v. split; [exact Hv|].
  apply (Hsub tvars venv Henv Hbenv Hfacts). exact Hinterp.
Qed.

(** Pair construction (ANF: first argument must be a variable). *)
Lemma sem_typed_pair_anf: forall tbounds tenv facts i e2 A B,
  sem_typed tbounds tenv facts (tvar i) A ->
  sem_typed tbounds tenv facts e2 B ->
  sem_typed tbounds tenv facts (tpair (tvar i) e2) (TSigma A (subst_ty TVar (abstract_term_var i) B)).
Proof.
  intros * Ha Hb tvars venv Henv Hbenv Hfacts.
  specialize (Ha tvars venv Henv Hbenv Hfacts).
  specialize (Hb tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv (tvar i)) as [[va|]|] eqn:Hevala; try discriminate.
  - destruct (Ha _ _ Hevala) as [va' [Hva' Hinterpa]].
    injection Hva' as <-.
    destruct (eval fuel' venv e2) as [[vb|]|] eqn:Hevalb; try discriminate.
    + destruct (Hb _ _ Hevalb) as [vb' [Hvb' Hinterpb]].
      injection Hvb' as <-.
      injection Heval as <-.
      exists (vpair va vb). split; [reflexivity|].
      simpl. unfold interp_sigma.
      exists va, vb. split; [reflexivity|]. split; [exact Hinterpa|].
      assert (Hnth: nth_error venv i = Some va).
      { destruct fuel'; [discriminate Hevala|].
        simpl in Hevala. destruct (nth_error venv i); congruence. }
      rewrite (interp_subst_term _ tvars venv i va Hnth).
      rewrite abstract_term_var_cancel. exact Hinterpb.
    + destruct (Hb _ _ Hevalb) as [? [Habs _]]; discriminate.
  - destruct (Ha _ _ Hevala) as [? [Habs _]]; discriminate.
Qed.

(** Pair elimination. *)
Lemma sem_typed_match_pair: forall tbounds tenv facts e A B body C z1 z2,
  sem_typed tbounds tenv facts e (TSigma A B) ->
  sem_typed (tbounds_shift_term (tbounds_shift_term tbounds)) (B :: A :: tenv) facts body C ->
  sem_typed tbounds tenv facts (tmatch_pair e body)
    (subst_ty TVar (z2 .: tvar) (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C)))).
Proof.
  intros * He Hbody tvars venv Henv Hbenv Hfacts.
  specialize (He tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv e) as [[ve|]|] eqn:Hevale; try discriminate.
  2: { destruct (He _ _ Hevale) as [? [Habs _]]; discriminate. }
  destruct (He _ _ Hevale) as [ve' [Hve' Hinterpe]].
  injection Hve' as <-.
  simpl in Hinterpe. unfold interp_sigma in Hinterpe.
  destruct Hinterpe as [v1 [v2 [Heq [Hinterp1 Hinterp2]]]].
  subst ve.
  (* Evaluate body in extended environment *)
  assert (Henv2: wf_env tvars (B :: A :: tenv) (v2 :: v1 :: venv)).
  { apply wf_env_cons; [|apply wf_env_cons; assumption]. exact Hinterp2. }
  assert (Hbenv2: wf_benv tvars (tbounds_shift_term (tbounds_shift_term tbounds)) (v2 :: v1 :: venv)).
  { apply wf_benv_double_shift_term. exact Hbenv. }
  assert (Hfacts2: wf_facts (v2 :: v1 :: venv) facts).
  { apply wf_facts_extend. apply wf_facts_extend. exact Hfacts. }
  specialize (Hbody tvars (v2 :: v1 :: venv) Henv2 Hbenv2 Hfacts2).
  destruct (Hbody _ _ Heval) as [v [Hv Hinterpv]].
  exists v. split; [exact Hv|].
  (* Step 1: avoid_var0 removes dependency on v2 (var 0) *)
  apply interp_avoid_var0 in Hinterpv.
  (* Step 2: shift from (v2 :: v1 :: venv) to (v1 :: venv) *)
  assert (H1: interp tvars (v1 :: venv)
    (subst_ty TVar (z1 .: tvar) (avoid_var0 C)) v).
  { rewrite (interp_env_shift_term _ tvars (v1 :: venv) v2).
    replace (ren_ty id S (subst_ty TVar (z1 .: tvar) (avoid_var0 C)))
      with (avoid_var0 C).
    2: { rewrite ren_subst_ty.
         transitivity (subst_ty TVar (fun n => tvar (S n))
                         (subst_ty TVar (z1 .: tvar) (avoid_var0 C))).
         - symmetry. exact (avoid_subst_shift_id C z1).
         - apply subst_ty_ext; intro n; unfold funcomp; reflexivity. }
    exact Hinterpv. }
  (* Step 3: avoid_var0 removes dependency on v1 (var 0) *)
  apply interp_avoid_var0 in H1.
  (* Step 4: shift from (v1 :: venv) to venv *)
  rewrite (interp_env_shift_term
    (subst_ty TVar (z2 .: tvar)
      (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C))))
    tvars venv v1).
  replace (ren_ty id S (subst_ty TVar (z2 .: tvar)
      (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C)))))
    with (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C))).
  2: { rewrite ren_subst_ty.
       transitivity (subst_ty TVar (fun n => tvar (S n))
         (subst_ty TVar (z2 .: tvar)
           (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C))))).
       - symmetry. exact (avoid_subst_shift_id
           (subst_ty TVar (z1 .: tvar) (avoid_var0 C)) z2).
       - apply subst_ty_ext; intro n; unfold funcomp; reflexivity. }
  exact H1.
Qed.

(** Left injection. *)
Lemma sem_typed_inl: forall tbounds tenv facts e A B,
  sem_typed tbounds tenv facts e A ->
  sem_typed tbounds tenv facts (tinl B e) (TSum A B).
Proof.
  intros * He tvars venv Henv Hbenv Hfacts.
  specialize (He tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv e) as [[ve|]|] eqn:Hevale; try discriminate.
  - destruct (He _ _ Hevale) as [ve' [Hve' Hinterpe]].
    injection Hve' as <-. injection Heval as <-.
    exists (vinl ve). split; [reflexivity|].
    simpl. unfold interp_sum. left. exists ve. auto.
  - destruct (He _ _ Hevale) as [? [Habs _]]; discriminate.
Qed.

(** Right injection. *)
Lemma sem_typed_inr: forall tbounds tenv facts e A B,
  sem_typed tbounds tenv facts e B ->
  sem_typed tbounds tenv facts (tinr A e) (TSum A B).
Proof.
  intros * He tvars venv Henv Hbenv Hfacts.
  specialize (He tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv e) as [[ve|]|] eqn:Hevale; try discriminate.
  - destruct (He _ _ Hevale) as [ve' [Hve' Hinterpe]].
    injection Hve' as <-. injection Heval as <-.
    exists (vinr ve). split; [reflexivity|].
    simpl. unfold interp_sum. right. exists ve. auto.
  - destruct (He _ _ Hevale) as [? [Habs _]]; discriminate.
Qed.

(** Sum elimination. *)
Lemma sem_typed_match_sum: forall tbounds tenv facts e A B body_l body_r C1 C2 zl zr,
  sem_typed tbounds tenv facts e (TSum A B) ->
  sem_typed (tbounds_shift_term tbounds) (A :: tenv)
    (((length tenv, e), (S (length tenv), tinl B (tvar 0))) :: facts) body_l C1 ->
  sem_typed (tbounds_shift_term tbounds) (B :: tenv)
    (((length tenv, e), (S (length tenv), tinr A (tvar 0))) :: facts) body_r C2 ->
  sem_typed tbounds tenv facts (tmatch_sum e body_l body_r)
    (TOr (subst_ty TVar (zl .: tvar) (avoid_var0 C1))
         (subst_ty TVar (zr .: tvar) (avoid_var0 C2))).
Proof.
  intros * He Hbl Hbr tvars venv Henv Hbenv Hfacts.
  specialize (He tvars venv Henv Hbenv Hfacts).
  intros fuel r Heval.
  destruct fuel as [|fuel']; [discriminate|].
  simpl in Heval.
  destruct (eval fuel' venv e) as [[ve|]|] eqn:Hevale; try discriminate.
  2: { destruct (He _ _ Hevale) as [? [Habs _]]; discriminate. }
  destruct (He _ _ Hevale) as [ve' [Hve' Hinterpe]].
  injection Hve' as <-.
  simpl in Hinterpe. unfold interp_sum in Hinterpe.
  destruct Hinterpe as [[w [Heq Ha]] | [w [Heq Hb]]]; subst ve.
  - (* vinl w *)
    assert (Henv1: wf_env tvars (A :: tenv) (w :: venv))
      by (apply wf_env_cons; assumption).
    assert (Hbenv1: wf_benv tvars (tbounds_shift_term tbounds) (w :: venv))
      by (apply wf_benv_shift_term; exact Hbenv).
    assert (Hfacts1: wf_facts (w :: venv)
      (((length tenv, e), (S (length tenv), tinl B (tvar 0))) :: facts)).
    { apply wf_facts_cons.
      - apply wf_env_length in Henv. simpl. lia.
      - apply wf_env_length in Henv. simpl. lia.
      - apply wf_env_length in Henv as Hlen.
        change (length (w :: venv)) with (S (length venv)).
        assert (H1: S (length venv) - length tenv = 1) by lia.
        assert (H2: S (length venv) - S (length tenv) = 0) by lia.
        rewrite H1, H2. simpl.
        exists (vinl w), fuel', 2.
        split; [exact Hevale | reflexivity].
      - apply wf_facts_extend. exact Hfacts. }
    specialize (Hbl tvars (w :: venv) Henv1 Hbenv1 Hfacts1).
    destruct (Hbl _ _ Heval) as [v [Hv Hinterpv]].
    exists v. split; [exact Hv|].
    simpl. unfold interp_or. left.
    apply interp_avoid_var0 in Hinterpv.
    rewrite (interp_env_shift_term _ tvars venv w).
    replace (ren_ty id S (subst_ty TVar (zl .: tvar) (avoid_var0 C1)))
      with (avoid_var0 C1).
    2: { rewrite ren_subst_ty.
         transitivity (subst_ty TVar (fun n => tvar (S n))
                         (subst_ty TVar (zl .: tvar) (avoid_var0 C1))).
         - symmetry. exact (avoid_subst_shift_id C1 zl).
         - apply subst_ty_ext; intro n; unfold funcomp; reflexivity. }
    exact Hinterpv.
  - (* vinr w *)
    assert (Henv1: wf_env tvars (B :: tenv) (w :: venv))
      by (apply wf_env_cons; assumption).
    assert (Hbenv1: wf_benv tvars (tbounds_shift_term tbounds) (w :: venv))
      by (apply wf_benv_shift_term; exact Hbenv).
    assert (Hfacts1: wf_facts (w :: venv)
      (((length tenv, e), (S (length tenv), tinr A (tvar 0))) :: facts)).
    { apply wf_facts_cons.
      - apply wf_env_length in Henv. simpl. lia.
      - apply wf_env_length in Henv. simpl. lia.
      - apply wf_env_length in Henv as Hlen.
        change (length (w :: venv)) with (S (length venv)).
        assert (H1: S (length venv) - length tenv = 1) by lia.
        assert (H2: S (length venv) - S (length tenv) = 0) by lia.
        rewrite H1, H2. simpl.
        exists (vinr w), fuel', 2.
        split; [exact Hevale | reflexivity].
      - apply wf_facts_extend. exact Hfacts. }
    specialize (Hbr tvars (w :: venv) Henv1 Hbenv1 Hfacts1).
    destruct (Hbr _ _ Heval) as [v [Hv Hinterpv]].
    exists v. split; [exact Hv|].
    simpl. unfold interp_or. right.
    apply interp_avoid_var0 in Hinterpv.
    rewrite (interp_env_shift_term _ tvars venv w).
    replace (ren_ty id S (subst_ty TVar (zr .: tvar) (avoid_var0 C2)))
      with (avoid_var0 C2).
    2: { rewrite ren_subst_ty.
         transitivity (subst_ty TVar (fun n => tvar (S n))
                         (subst_ty TVar (zr .: tvar) (avoid_var0 C2))).
         - symmetry. exact (avoid_subst_shift_id C2 zr).
         - apply subst_ty_ext; intro n; unfold funcomp; reflexivity. }
    exact Hinterpv.
Qed.

