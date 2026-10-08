(** * Semantic Typing (§3.4, Figures 8 and 9)

    The semantic typing judgment Γ ⊨ a : A ([sem_typed], Figure 8), and one
    soundness lemma per typing rule of Figure 9. Composing these lemmas
    along any derivation is the fundamental theorem of the logical
    relation.

    Note: the paper's rules T-True and T-False assign the singleton types
    [True]/[False]; the mechanization has a single [TBool] and one rule
    [sem_typed_bool]. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.EvalLemmas.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.InterpLemmas.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.WfLemmas.
Require Import RefinementTypes.Avoid.
Require Import RefinementTypes.AvoidLemmas.
Require Import RefinementTypes.FirstOrder.
Require Import RefinementTypes.FirstOrderLemmas.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.PositivityLemmas.
Require Import RefinementTypes.SemanticSubtyping.

(** ** The judgment (Figure 8) *)

(** Semantic typing: a term [t] has type [T] if, in any well-formed
    environment, whenever the evaluation of [t] terminates, it produces a
    value in the interpretation of [T] (partial correctness). *)
Definition sem_typed (gamma: Ctx) (t: Term) (T: Ty) : Prop :=
  forall tvars venv,
    wf_ctx tvars gamma venv ->
    term_has_semtype venv t (interp tvars venv T).

(** ** Proof tactics *)

(** Case on the fuel of the evaluation hypothesis: with no fuel there is no
    result; otherwise expose one evaluation step. *)
Local Ltac fuel_step :=
  match goal with
  | Heval : eval ?fuel _ _ = Some _ |- _ =>
      destruct fuel as [|fuel]; [discriminate Heval |]; simpl in Heval
  end.

(** Case on the result of the sub-evaluation of [e] occurring in the
    evaluation hypothesis, using the semantic typing hypothesis [He] for
    [e]. A timeout propagates and a stuck result contradicts [He]; the
    value case continues with [Hv : interp _ _ _ v] and the evaluation
    equation [Hev]. *)
Local Ltac sem_step He e v Hv Hev :=
  match goal with
  | _ : context [eval ?fuel ?venv e] |- _ =>
      destruct (eval fuel venv e) as [[v|]|] eqn:Hev; try discriminate;
      [ let Hr := fresh "Hr" in
        destruct (He _ _ Hev) as [? [Hr Hv]]; injection Hr as <-
      | destruct (He _ _ Hev) as [? [? _]]; discriminate ]
  end.

(** ** Constants *)

(** [tdiverge] never terminates, so it vacuously has every type. (No
    counterpart in Figure 9: the paper's core syntax leaves "diverge"
    informal.) *)
Lemma sem_typed_diverge: forall gamma T, sem_typed gamma tdiverge T.
Proof.
  intros gamma T tvars venv Hwf fuel r Heval. destruct fuel; discriminate.
Qed.

(** T-Unit *)
Lemma sem_typed_unit: forall gamma, sem_typed gamma tunit TUnit.
Proof.
  intros gamma tvars venv Hwf fuel r Heval. fuel_step. injection Heval as <-.
  exists vunit. simpl. auto.
Qed.

(** T-True/T-False (merged: booleans have type [TBool]) *)
Lemma sem_typed_bool: forall gamma b, sem_typed gamma (tbool b) TBool.
Proof.
  intros gamma b tvars venv Hwf fuel r Heval. fuel_step. injection Heval as <-.
  exists (vbool b). simpl. split; [reflexivity|]. exists b. reflexivity.
Qed.

(** T-Int *)
Lemma sem_typed_int32: forall gamma z, sem_typed gamma (tint32 z) TInt32.
Proof.
  intros gamma z tvars venv Hwf fuel r Heval. fuel_step. injection Heval as <-.
  exists (vint32 z). simpl. split; [reflexivity|]. exists z. reflexivity.
Qed.

(** ** Variables, functions, and polymorphism *)

(** T-Var: the looked-up type is shifted past the [S i] bindings introduced
    after it. *)
Lemma sem_typed_var: forall gamma i T,
  nth_error (ctx_tenv gamma) i = Some T ->
  sem_typed gamma (tvar i) (subst_ty TVar (tm_shift (S i)) T).
Proof.
  intros gamma i T Hnth tvars venv Hwf.
  destruct (wf_ctx_lookup_term _ _ _ _ _ Hwf Hnth) as [v [Hvnth Hinterp]].
  intros fuel r Heval. fuel_step. rewrite Hvnth in Heval. injection Heval as <-.
  exists v. split; [reflexivity|].
  (* [T] is interpreted in the suffix [skipn (S i) venv]; weaken to [venv]. *)
  change (tm_shift (S i)) with (upn_tm 0 (tm_shift (S i))). rewrite subst_ty_shift_ren.
  rewrite <- (interp_ren T tvars (skipn (S i) venv) tvars venv id (shift_ren 0 (S i)));
    [exact Hinterp | intro x; reflexivity |].
  intro x. unfold shift_ren. destruct (lt_dec x 0); [lia|].
  rewrite nth_error_skipn. f_equal. lia.
Qed.

(** T-Abs *)
Lemma sem_typed_abs: forall gamma A b B,
  sem_typed (ctx_cons_term gamma A) b B ->
  sem_typed gamma (tabs A b) (TFun A B).
Proof.
  intros gamma A b B Hbody tvars venv Hwf fuel r Heval. fuel_step. injection Heval as <-.
  exists (vabs venv b). split; [reflexivity|].
  simpl. unfold interp_fun. exists venv, b. split; [reflexivity|].
  intros arg Harg. apply (Hbody tvars (arg :: venv)). apply wf_ctx_cons_term; assumption.
Qed.

(** T-App (ANF: the argument must be a variable, which is substituted for
    the bound variable in the dependent result type). *)
Lemma sem_typed_app_anf: forall gamma fn i A B,
  sem_typed gamma fn (TFun A B) ->
  sem_typed gamma (tvar i) A ->
  sem_typed gamma (tapp fn (tvar i)) (subst_ty TVar (tvar i .: tvar) B).
Proof.
  intros gamma fn i A B Hfn Ha tvars venv Hwf.
  specialize (Hfn tvars venv Hwf). specialize (Ha tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step Hfn fn vf Hinterpf Hevalfn.
  destruct Hinterpf as [envf [body [-> Hbody]]].
  sem_step Ha (tvar i) va Hinterpa Hevala.
  destruct (Hbody va Hinterpa _ _ Heval) as [v [Hv Hvb]].
  exists v. split; [exact Hv|].
  assert (Hnth: nth_error venv i = Some va).
  { destruct fuel; [discriminate Hevala|]. simpl in Hevala. destruct (nth_error venv i); congruence. }
  rewrite <- (interp_subst_term B tvars venv i va Hnth). exact Hvb.
Qed.

(** T-TAbs *)
Lemma sem_typed_tabs: forall gamma L U b A,
  sem_typed (ctx_cons_type gamma L U) b A ->
  sem_typed gamma (ttabs L U b) (TForall L U A).
Proof.
  intros gamma L U b A Hbody tvars venv Hwf fuel r Heval. fuel_step. injection Heval as <-.
  exists (vtabs venv b). split; [reflexivity|].
  simpl. unfold interp_forall. exists venv, b. split; [reflexivity|].
  intros X HL HU. apply (Hbody (X :: tvars) venv). apply wf_ctx_cons_type; assumption.
Qed.

(** T-TApp: type application uses semantic substitution. *)
Lemma sem_typed_tapp: forall gamma fn L U A B,
  sem_typed gamma fn (TForall L U B) ->
  sem_subtype gamma L A ->
  sem_subtype gamma A U ->
  sem_typed gamma (ttapp fn A) (ty_subst B A).
Proof.
  intros gamma fn L U A B Hfn HsubL HsubU tvars venv Hwf.
  specialize (Hfn tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step Hfn fn vf Hinterpf Hevalfn.
  destruct Hinterpf as [envf [body [-> Hbody]]].
  rewrite <- interp_subst.
  exact (Hbody (interp tvars venv A) (HsubL tvars venv Hwf) (HsubU tvars venv Hwf) _ _ Heval).
Qed.

(** ** Let bindings and control flow *)

(** T-Let: the body is typed with the equality fact [x ~ e]; the bound
    variable is removed from the result type by [avoid_var0]. *)
Lemma sem_typed_let: forall gamma e A b B z,
  sem_typed gamma e A ->
  sem_typed (ctx_add_fact (ctx_cons_term gamma A) ((S (ctx_len gamma), tvar 0), (ctx_len gamma, e))) b B ->
  sem_typed gamma (tlet A e b) (subst_ty TVar (z .: tvar) (avoid_var0 B)).
Proof.
  intros gamma e A b B z He Hb tvars venv Hwf.
  specialize (He tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step He e ve Hinterpe Hevale.
  destruct (Hb tvars (ve :: venv) (wf_ctx_fact_let _ _ _ _ _ _ _ Hwf Hinterpe Hevale) _ _ Heval)
    as [v [Hv Hinterpv]].
  exists v. split; [exact Hv|].
  apply (interp_avoid_var0_subst B tvars venv ve z v). exact Hinterpv.
Qed.

(** T-BinOp *)
Lemma sem_typed_bin_op: forall gamma op a b T,
  sem_typed gamma a T ->
  sem_typed gamma b T ->
  bin_op_ty_compat op T = true ->
  sem_typed gamma (tbin_op op a b) (bin_op_result_ty op T).
Proof.
  intros gamma op a b T Ha Hb Hcompat tvars venv Hwf.
  specialize (Ha tvars venv Hwf). specialize (Hb tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step Ha a va Hinterpa Hevala.
  sem_step Hb b vb Hinterpb Hevalb.
  destruct (eval_bin_op_defined op va vb
    (bin_op_ty_interp_val_pair_compat op T tvars venv va vb Hcompat Hinterpa Hinterpb)) as [v Hop].
  rewrite Hop in Heval. injection Heval as <-.
  exists v. split; [reflexivity|].
  exact (eval_bin_op_result_in_interp op T tvars venv va vb v Hcompat Hinterpa Hinterpb Hop).
Qed.

(** T-If: each branch is typed with an equality fact recording the value of
    the condition. *)
Lemma sem_typed_if: forall gamma c t e T1 T2,
  sem_typed gamma c TBool ->
  sem_typed (ctx_add_fact gamma ((ctx_len gamma, c), (ctx_len gamma, tbool true))) t T1 ->
  sem_typed (ctx_add_fact gamma ((ctx_len gamma, c), (ctx_len gamma, tbool false))) e T2 ->
  sem_typed gamma (tif c t e) (TOr T1 T2).
Proof.
  intros gamma c t e T1 T2 Hc Ht He tvars venv Hwf.
  specialize (Hc tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step Hc c vc Hinterpc Hevalc.
  destruct Hinterpc as [b ->]. destruct b.
  - destruct (Ht tvars venv (wf_ctx_fact_if _ _ _ _ _ _ Hwf Hevalc) _ _ Heval) as [v [Hv Hinterpv]].
    exists v. split; [exact Hv|]. left. exact Hinterpv.
  - destruct (He tvars venv (wf_ctx_fact_if _ _ _ _ _ _ Hwf Hevalc) _ _ Heval) as [v [Hv Hinterpv]].
    exists v. split; [exact Hv|]. right. exact Hinterpv.
Qed.

(** T-Loop. The conditions [HclA] and [HclB] require that [A] and [B] have no
    free term variables, so that [interp] is invariant under environment
    extension. *)
Lemma sem_typed_loop: forall gamma a A body B,
  ren_ty id S A = A ->
  ren_ty id S B = B ->
  sem_typed gamma a A ->
  sem_typed (ctx_cons_term gamma A) body (TSum A B) ->
  sem_typed gamma (tloop a body) B.
Proof.
  intros gamma a A body B HclA HclB Ha Hbody tvars venv Hwf.
  specialize (Ha tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step Ha a va Hinterpa Hevala.
  eapply run_loop_typed; [exact Hinterpa | | exact Heval].
  intros v HAv r0 Hr0.
  destruct (Hbody tvars (v :: venv) (wf_ctx_cons_term _ _ _ _ _ HAv Hwf) _ _ Hr0)
    as [w [Hw Hinterpw]].
  exists w. split; [exact Hw|].
  destruct Hinterpw as [[u [-> HA]] | [u [-> HB]]]; simpl.
  - rewrite (interp_env_ren_term A tvars venv v), HclA. exact HA.
  - rewrite (interp_env_ren_term B tvars venv v), HclB. exact HB.
Qed.

(** ** Selfification and subsumption *)

(** T-Self (selfification): if e has first-order type T, then e also has
    the singleton type {x: T | x == e}. *)
Lemma sem_typed_selfify: forall gamma e T,
  sem_typed gamma e T ->
  fo T = true ->
  sem_typed gamma e (TRefine T (tbin_op OpEq (tvar 0) (ren_tm id S e))).
Proof.
  intros gamma e T Htyped Hfo tvars venv Hwf.
  specialize (Htyped tvars venv Hwf).
  intros fuel r Heval.
  destruct (Htyped fuel r Heval) as [v [-> Hinterp]].
  exists v. split; [reflexivity|].
  split; [exact Hinterp|].
  pose proof (fo_interp_is_fo_val T tvars venv v Hfo Hinterp) as Hfov.
  (* In [v :: venv], [tvar 0] evaluates to [v], and so does the shifted [e]
     by weakening (Lemma 3.7), since [v] is first-order. *)
  assert (Hren: ren_tm id S e = subst_tm TVar (tm_shift 1) e).
  { rewrite ren_subst_tm. apply subst_tm_ext; [reflexivity |].
    intro n. unfold funcomp, tm_shift. f_equal. lia. }
  pose proof (eval_shift_rel fuel e [] [v] venv) as Hrc.
  simpl in Hrc. rewrite Heval, <- Hren in Hrc.
  pose proof (res_rel_fo _ _ Hfov Hrc) as Heval_e.
  pose proof (eval_tbin_op 1 fuel (v :: venv) OpEq (tvar 0) (ren_tm id S e) v v (vbool true)
    eq_refl Heval_e (eval_bin_op_eq_refl v Hfov)) as Heval_eq.
  (* Evaluation is deterministic up to fuel, so every successful evaluation
     of the predicate gives [true]. *)
  intros fuel2 r2 Heval2.
  destruct (Nat.le_ge_cases fuel2 (S (1 + fuel))) as [Hle | Hge].
  - apply (eval_fuel_mono _ _ _ _ _ Hle) in Heval2.
    rewrite Heval_eq in Heval2. injection Heval2 as <-.
    exists (vbool true). auto.
  - apply (eval_fuel_mono _ _ _ _ _ Hge) in Heval_eq.
    rewrite Heval_eq in Heval2. injection Heval2 as <-.
    exists (vbool true). auto.
Qed.

(** T-Sub *)
Lemma sem_typed_sub: forall gamma t A B,
  sem_typed gamma t A ->
  sem_subtype gamma A B ->
  sem_typed gamma t B.
Proof.
  intros gamma t A B Htyped Hsub tvars venv Hwf.
  eapply term_has_semtype_mono; [apply (Hsub tvars venv Hwf) | exact (Htyped tvars venv Hwf)].
Qed.

(** ** Pairs and sums *)

(** T-Pair (ANF: the first component must be a variable, which is
    abstracted out of the second component's type). *)
Lemma sem_typed_pair_anf: forall gamma i e2 A B,
  sem_typed gamma (tvar i) A ->
  sem_typed gamma e2 B ->
  sem_typed gamma (tpair (tvar i) e2) (TSigma A (subst_ty TVar (abstract_term_var i) B)).
Proof.
  intros gamma i e2 A B Ha Hb tvars venv Hwf.
  specialize (Ha tvars venv Hwf). specialize (Hb tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step Ha (tvar i) va Hinterpa Hevala.
  sem_step Hb e2 vb Hinterpb Hevalb.
  injection Heval as <-.
  exists (vpair va vb). split; [reflexivity|].
  simpl. unfold interp_sigma.
  exists va, vb. split; [reflexivity|]. split; [exact Hinterpa|].
  assert (Hnth: nth_error venv i = Some va).
  { destruct fuel; [discriminate Hevala|]. simpl in Hevala. destruct (nth_error venv i); congruence. }
  rewrite (interp_subst_term _ tvars venv i va Hnth), abstract_term_var_cancel. exact Hinterpb.
Qed.

(** T-MatchPair *)
Lemma sem_typed_match_pair: forall gamma e A B body C z1 z2,
  sem_typed gamma e (TSigma A B) ->
  sem_typed (ctx_cons_term (ctx_cons_term gamma A) B) body C ->
  sem_typed gamma (tmatch_pair e body)
    (subst_ty TVar (z2 .: tvar) (avoid_var0 (subst_ty TVar (z1 .: tvar) (avoid_var0 C)))).
Proof.
  intros gamma e A B body C z1 z2 He Hbody tvars venv Hwf.
  specialize (He tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step He e ve Hinterpe Hevale.
  destruct Hinterpe as [v1 [v2 [-> [Hinterp1 Hinterp2]]]].
  destruct (Hbody tvars (v2 :: v1 :: venv)
    (wf_ctx_cons_term _ _ _ _ _ Hinterp2 (wf_ctx_cons_term _ _ _ _ _ Hinterp1 Hwf)) _ _ Heval)
    as [v [Hv Hinterpv]].
  exists v. split; [exact Hv|].
  apply (interp_avoid_var0_subst _ tvars venv v1 z2 v).
  apply (interp_avoid_var0_subst _ tvars (v1 :: venv) v2 z1 v).
  exact Hinterpv.
Qed.

(** T-Inl *)
Lemma sem_typed_inl: forall gamma e A B,
  sem_typed gamma e A ->
  sem_typed gamma (tinl B e) (TSum A B).
Proof.
  intros gamma e A B He tvars venv Hwf.
  specialize (He tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step He e ve Hinterpe Hevale.
  injection Heval as <-.
  exists (vinl ve). split; [reflexivity|]. left. exists ve. auto.
Qed.

(** T-Inr *)
Lemma sem_typed_inr: forall gamma e A B,
  sem_typed gamma e B ->
  sem_typed gamma (tinr A e) (TSum A B).
Proof.
  intros gamma e A B He tvars venv Hwf.
  specialize (He tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step He e ve Hinterpe Hevale.
  injection Heval as <-.
  exists (vinr ve). split; [reflexivity|]. right. exists ve. auto.
Qed.

(** T-MatchSum: each branch is typed with an equality fact recording the
    scrutinee's shape. *)
Lemma sem_typed_match_sum: forall gamma e A B body_l body_r C1 C2 zl zr,
  sem_typed gamma e (TSum A B) ->
  sem_typed (ctx_add_fact (ctx_cons_term gamma A) ((ctx_len gamma, e), (S (ctx_len gamma), tinl B (tvar 0))))
    body_l C1 ->
  sem_typed (ctx_add_fact (ctx_cons_term gamma B) ((ctx_len gamma, e), (S (ctx_len gamma), tinr A (tvar 0))))
    body_r C2 ->
  sem_typed gamma (tmatch_sum e body_l body_r)
    (TOr (subst_ty TVar (zl .: tvar) (avoid_var0 C1))
         (subst_ty TVar (zr .: tvar) (avoid_var0 C2))).
Proof.
  intros gamma e A B body_l body_r C1 C2 zl zr He Hbl Hbr tvars venv Hwf.
  specialize (He tvars venv Hwf).
  intros fuel r Heval. fuel_step.
  sem_step He e ve Hinterpe Hevale.
  destruct Hinterpe as [[w [-> Hw]] | [w [-> Hw]]].
  - destruct (Hbl tvars (w :: venv)
      (wf_ctx_fact_match _ _ _ _ _ (tinl B (tvar 0)) _ _ _ 2 Hwf Hw Hevale eq_refl) _ _ Heval)
      as [v [Hv Hinterpv]].
    exists v. split; [exact Hv|]. left.
    apply (interp_avoid_var0_subst _ tvars venv w zl v). exact Hinterpv.
  - destruct (Hbr tvars (w :: venv)
      (wf_ctx_fact_match _ _ _ _ _ (tinr A (tvar 0)) _ _ _ 2 Hwf Hw Hevale eq_refl) _ _ Heval)
      as [v [Hv Hinterpv]].
    exists v. split; [exact Hv|]. right.
    apply (interp_avoid_var0_subst _ tvars venv w zr v). exact Hinterpv.
Qed.
