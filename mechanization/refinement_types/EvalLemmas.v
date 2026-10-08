(** * Evaluation Lemmas

    Properties of the interpreter: fuel monotonicity (more fuel preserves
    any terminating result, which also gives determinism up to fuel), a
    typed invariant for [run_loop], definedness of [eval_bin_op] on
    compatible operands, and evaluation under renaming (Lemma 3.7 and
    §3.6): inserting values in the environment, or replacing an entry by
    a reference to another one, preserves evaluation results up to a
    compatibility relation on closures. The file also defines
    [eval_to_true], the predicate behind refinement types, and proves it
    invariant under type erasure, weakening and substitution. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
From Stdlib Require Import ZArith.BinInt.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.EvalTypeErasure.
Require Import RefinementTypes.Tactics.

(** ** Fuel monotonicity for run_loop *)
Lemma run_loop_mono : forall step1 step2 n1 n2 va r,
  n1 <= n2 ->
  (forall v r, step1 v = Some r -> step2 v = Some r) ->
  run_loop step1 n1 va = Some r ->
  run_loop step2 n2 va = Some r.
Proof.
  intros step1 step2 n1.
  induction n1; intros; try discriminate.
  destruct n2; [lia|].
  simpl in *.
  destruct (step1 va) as [[v|]|] eqn:Hs; try discriminate.
  - assert (Hs2 := H0 _ _ Hs). rewrite Hs2.
    destruct v; try (exact H1);
      try (eapply IHn1; [lia | eauto | eauto]).
  - assert (Hs2 := H0 _ _ Hs). rewrite Hs2. exact H1.
Qed.

(** ** Type preservation for run_loop *)
Lemma run_loop_typed : forall step n va (A B : Value -> Prop),
  A va ->
  (forall v, A v -> forall r, step v = Some r ->
    exists w, r = Some w /\
      match w with
      | vinl u => A u
      | vinr u => B u
      | _ => False
      end) ->
  forall r, run_loop step n va = Some r ->
  exists v, r = Some v /\ B v.
Proof.
  intros step n.
  induction n; intros va A B HAva Hstep r Hloop.
  - discriminate.
  - simpl in Hloop.
    destruct (step va) as [[w|]|] eqn:Hs; try discriminate.
    + destruct (Hstep va HAva _ Hs) as [w' [Hw' HwP]].
      injection Hw' as <-.
      destruct w;
        try (simpl in HwP; contradiction).
      (* vinl case - continue *)
      * eapply IHn; [exact HwP | exact Hstep | exact Hloop].
      (* vinr case - break *)
      * injection Hloop as <-.
        eexists. split; [reflexivity | exact HwP].
    + injection Hloop as <-.
      destruct (Hstep va HAva _ Hs) as [w' [Hw' _]]. discriminate.
Qed.

(** ** Fuel monotonicity *)
Lemma eval_fuel_mono: forall fuel1 fuel2 env t r,
  fuel1 <= fuel2 ->
  eval fuel1 env t = Some r ->
  eval fuel2 env t = Some r.
Proof.
  induction fuel1; intros; try discriminate.
  destruct fuel2; try lia.
  assert (fuel1 <= fuel2) by lia.
  destruct t; auto; simpl in *;
    try (repeat (repeat prune_branches; erewrite IHfuel1; eauto); fail).
  (* tloop *)
  destruct (eval fuel1 env t1) as [[va|]|] eqn:Ha.
  -- assert (Ha2 : eval fuel2 env t1 = Some (Some va)) by (eapply IHfuel1; eauto).
     rewrite Ha2.
     eapply run_loop_mono; [eauto | | eauto].
     intros. eapply IHfuel1; eauto.
  -- assert (Ha2 : eval fuel2 env t1 = Some None) by (eapply IHfuel1; eauto).
     rewrite Ha2. exact H0.
  -- discriminate.
Qed.

(** ** Evaluation of binary operations *)

(** General tbin_op evaluation: if both sides evaluate and eval_bin_op succeeds. *)
Lemma eval_tbin_op: forall fuel1 fuel2 env op a b va vb v,
  eval fuel1 env a = Some (Some va) ->
  eval fuel2 env b = Some (Some vb) ->
  eval_bin_op op va vb = Some v ->
  eval (S (fuel1 + fuel2)) env (tbin_op op a b) = Some (Some v).
Proof.
  intros. simpl.
  rewrite eval_fuel_mono with (fuel1 := fuel1) (r := Some va); try lia; auto.
  rewrite eval_fuel_mono with (fuel1 := fuel2) (r := Some vb); try lia; auto.
  rewrite H1. reflexivity.
Qed.

(** Equality via eval_bin_op is defined on all pairs of first-order values. *)
Lemma eval_bin_op_eq_fo_defined: forall va vb,
  fo_val va -> fo_val vb ->
  exists r, eval_bin_op OpEq va vb = Some r.
Proof.
  intros va vb [-> | [[b1 ->] | [z1 ->]]] [-> | [[b2 ->] | [z2 ->]]];
  simpl; eauto.
Qed.

(** Equality is reflexive on first-order values. *)
Lemma eval_bin_op_eq_refl: forall v, fo_val v -> eval_bin_op OpEq v v = Some (vbool true).
Proof.
  intros v [Hunit | [Hbool | Hint32]].
  - subst. reflexivity.
  - destruct Hbool as [b ->]. simpl. rewrite Bool.eqb_reflx. reflexivity.
  - destruct Hint32 as [z ->]. simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** eval_bin_op is defined on compatible value pairs. *)
Lemma eval_bin_op_defined: forall op va vb,
  bin_op_val_pair_compat op va vb ->
  exists r, eval_bin_op op va vb = Some r.
Proof.
  intros op va vb Hcompat.
  destruct op; simpl in *;
    first [ destruct Hcompat as [z1 [z2 [-> ->]]];
            simpl; eauto
          | destruct Hcompat as [b1 [b2 [-> ->]]];
            simpl; eauto
          | destruct Hcompat as [Hva Hvb];
            destruct Hva as [-> | [[b1 ->] | [z1 ->]]];
            destruct Hvb as [-> | [[b2 ->] | [z2 ->]]];
            simpl; eauto ].
Qed.

(** ** Evaluation under renaming (Lemma 3.7 and §3.6)

    Weakening (inserting values in the middle of the environment, with the
    matching de Bruijn shift on the term) and substitution (replacing an
    environment entry by a reference [tvar i] to another entry) are both
    instances of one simulation: evaluating [ren_tm zeta xi1 t] in [env1]
    and [ren_tm zeta xi2 t] in [env2] give related results whenever the
    two environments agree pointwise through the renamings, i.e. looking
    up [xi1 x] in [env1] and [xi2 x] in [env2] gives either nothing on
    both sides or related values ([env_rel]). The type renaming [zeta] is
    irrelevant to evaluation and is only carried along so that closures
    created under type binders have the same shape as the others.

    Results are not preserved exactly, because closures capture the
    extended environment. They are preserved up to [res_rel] (written ≈
    in the paper): timeouts and stuck states match, first-order values
    are equal, and closures are related when their captured environments
    are, again through a pair of renamings. The statement is symmetric in
    its two sides, so both directions of each corollary are instances of
    the same lemma. *)

(** *** Relations *)

Inductive val_rel : Value -> Value -> Prop :=
| vr_unit : val_rel vunit vunit
| vr_bool : forall b, val_rel (vbool b) (vbool b)
| vr_int32 : forall z, val_rel (vint32 z) (vint32 z)
| vr_pair : forall v1 v1' v2 v2',
    val_rel v1 v1' -> val_rel v2 v2' ->
    val_rel (vpair v1 v2) (vpair v1' v2')
| vr_inl : forall v v', val_rel v v' -> val_rel (vinl v) (vinl v')
| vr_inr : forall v v', val_rel v v' -> val_rel (vinr v) (vinr v')
| vr_abs : forall env1 xi1 env2 xi2 zeta body,
    (forall x, lookup_rel env1 (xi1 x) env2 (xi2 x)) ->
    val_rel (vabs env1 (ren_tm zeta (upren xi1) body))
            (vabs env2 (ren_tm zeta (upren xi2) body))
| vr_tabs : forall env1 xi1 env2 xi2 zeta body,
    (forall x, lookup_rel env1 (xi1 x) env2 (xi2 x)) ->
    val_rel (vtabs env1 (ren_tm zeta xi1 body))
            (vtabs env2 (ren_tm zeta xi2 body))
with lookup_rel : list Value -> var -> list Value -> var -> Prop :=
| lr_none : forall env1 y1 env2 y2,
    nth_error env1 y1 = None -> nth_error env2 y2 = None ->
    lookup_rel env1 y1 env2 y2
| lr_some : forall env1 y1 env2 y2 v1 v2,
    nth_error env1 y1 = Some v1 -> nth_error env2 y2 = Some v2 ->
    val_rel v1 v2 ->
    lookup_rel env1 y1 env2 y2.

(** Two environments agree pointwise through a pair of renamings. *)
Definition env_rel (env1 : list Value) (xi1 : var -> var)
                   (env2 : list Value) (xi2 : var -> var) : Prop :=
  forall x, lookup_rel env1 (xi1 x) env2 (xi2 x).

Inductive res_rel : option (option Value) -> option (option Value) -> Prop :=
| rr_timeout : res_rel None None
| rr_stuck : res_rel (Some None) (Some None)
| rr_val : forall v1 v2, val_rel v1 v2 -> res_rel (Some (Some v1)) (Some (Some v2)).

(** *** Basic properties *)

(** Going under a binder: cons related values, lift both renamings. *)
Lemma env_rel_cons : forall v1 v2 env1 xi1 env2 xi2,
  val_rel v1 v2 ->
  env_rel env1 xi1 env2 xi2 ->
  env_rel (v1 :: env1) (upren xi1) (v2 :: env2) (upren xi2).
Proof.
  intros v1 v2 env1 xi1 env2 xi2 Hv Henv [|x]; unfold upren, scons, funcomp.
  - eapply lr_some; simpl; eauto.
  - pose proof (Henv x) as Hl.
    inversion Hl as [? ? ? ? E1 E2 | ? ? ? ? ? ? E1 E2 Hv']; subst;
      [apply lr_none | eapply lr_some]; simpl; eauto.
Qed.

Lemma Forall_val_rel_nth_error : forall env x v,
  Forall (fun v => val_rel v v) env ->
  nth_error env x = Some v ->
  val_rel v v.
Proof.
  induction env as [|a env IH]; intros [|x] v Hall E; simpl in E;
    try discriminate; inversion Hall; subst.
  - injection E as <-. assumption.
  - eauto.
Qed.

Lemma env_rel_refl : forall env,
  Forall (fun v => val_rel v v) env ->
  env_rel env id env id.
Proof.
  intros env Hall x. unfold id.
  destruct (nth_error env x) as [v|] eqn:E.
  - eapply lr_some; eauto using Forall_val_rel_nth_error.
  - apply lr_none; assumption.
Qed.

Lemma val_rel_refl : forall v, val_rel v v.
Proof.
  induction v as [| b | z | v1 v2 IH1 IH2 | v IH | v IH | venv body IH | venv body IH]
    using Value_ind_nested; try (constructor; assumption).
  - replace body with (ren_tm id (upren id) body)
      by (rewrite ren_tm_upren_id; apply ren_tm_id).
    apply vr_abs. exact (env_rel_refl venv IH).
  - replace body with (ren_tm id id body) by apply ren_tm_id.
    apply vr_tabs. exact (env_rel_refl venv IH).
Qed.

(** Pointwise equal lookups give related environments. This is where the
    corollaries below get both orientations for free: an equation is
    symmetric. *)
Lemma env_rel_of_nth_eq : forall env1 xi1 env2 xi2,
  (forall x, nth_error env1 (xi1 x) = nth_error env2 (xi2 x)) ->
  env_rel env1 xi1 env2 xi2.
Proof.
  intros env1 xi1 env2 xi2 Heq x. specialize (Heq x).
  destruct (nth_error env1 (xi1 x)) as [v|] eqn:E1;
    try rewrite E1 in Heq; symmetry in Heq.
  - eapply lr_some; eauto using val_rel_refl.
  - apply lr_none; assumption.
Qed.

(** On first-order values the relation is equality. *)
Lemma val_rel_fo : forall v v', fo_val v -> val_rel v v' -> v' = v.
Proof.
  intros v v' [-> | [[b ->] | [z ->]]] H; inversion H; subst; reflexivity.
Qed.

Lemma res_rel_fo : forall v r,
  fo_val v -> res_rel (Some (Some v)) r -> r = Some (Some v).
Proof.
  intros v r Hfo H. inversion H; subst. f_equal. f_equal.
  eapply val_rel_fo; eassumption.
Qed.

Lemma eval_bin_op_val_rel : forall op va va' vb vb',
  val_rel va va' -> val_rel vb vb' ->
  eval_bin_op op va vb = eval_bin_op op va' vb'.
Proof.
  intros op va va' vb vb' Hva Hvb.
  destruct va; inversion Hva; subst; destruct vb; inversion Hvb; subst;
    destruct op; reflexivity.
Qed.

Lemma run_loop_rel : forall step1 step2 n va va',
  val_rel va va' ->
  (forall v v', val_rel v v' -> res_rel (step1 v) (step2 v')) ->
  res_rel (run_loop step1 n va) (run_loop step2 n va').
Proof.
  intros step1 step2 n.
  induction n; intros va va' Hva Hstep; simpl; [constructor|].
  pose proof (Hstep va va' Hva) as H.
  remember (step1 va) as r1. remember (step2 va') as r2.
  destruct H as [| | v1 v2 Hv]; try constructor.
  destruct v1; inversion Hv; subst; try constructor; auto.
Qed.

(** *** The simulation *)

(** Apply the induction hypothesis [IH] to the sub-evaluation of [t] and
    case on the related results. The timeout and stuck cases close
    immediately; the value case is left with [v1 v2 : Value] and
    [Hv : val_rel v1 v2] in context. *)
Local Ltac sim IH t Henv :=
  match goal with
  | |- context [ren_tm ?zeta _ t] =>
      let H := fresh "Hsim" in
      pose proof (IH t zeta _ _ _ _ Henv) as H;
      let ra := fresh "ra" in
      let rb := fresh "rb" in
      match type of H with
      | res_rel ?a ?b => remember a as ra; remember b as rb
      end;
      destruct H as [ | | ?v1 ?v2 ?Hv]; simpl; try solve [constructor]
  end.

(** Case on the shape of the most recently related value pair, closing
    all branches where evaluation gets stuck on both sides. *)
Local Ltac sim_val :=
  match goal with
  | Hv : val_rel ?v1 _ |- _ =>
      is_var v1; destruct v1; inversion Hv; subst; simpl; try solve [constructor]
  end.

Lemma eval_ren_rel : forall fuel t zeta env1 xi1 env2 xi2,
  env_rel env1 xi1 env2 xi2 ->
  res_rel (eval fuel env1 (ren_tm zeta xi1 t)) (eval fuel env2 (ren_tm zeta xi2 t)).
Proof.
  induction fuel as [|fuel IH]; intros t zeta env1 xi1 env2 xi2 Henv;
    [simpl; constructor|].
  destruct t as [|b|z|x|A b|f a|L U b|f A|A e b|e1 e2|e b|B e|A e|e bl br|op a b|c t1 t2| |a b];
    simpl.
  - (* tunit *) constructor; constructor.
  - (* tbool *) constructor; constructor.
  - (* tint32 *) constructor; constructor.
  - (* tvar *)
    pose proof (Henv x) as Hl.
    inversion Hl as [? ? ? ? E1 E2 | ? ? ? ? ? ? E1 E2 Hv]; subst;
      rewrite E1, E2; simpl; constructor; assumption.
  - (* tabs *) constructor. apply vr_abs. exact Henv.
  - (* tapp *)
    sim IH f Henv. sim_val.
    sim IH a Henv.
    apply IH, env_rel_cons; assumption.
  - (* ttabs *) constructor. apply vr_tabs. exact Henv.
  - (* ttapp *)
    sim IH f Henv. sim_val.
    apply IH. assumption.
  - (* tlet *)
    sim IH e Henv.
    apply IH, env_rel_cons; assumption.
  - (* tpair *)
    sim IH e1 Henv. sim IH e2 Henv.
    constructor. constructor; assumption.
  - (* tmatch_pair *)
    sim IH e Henv. sim_val.
    apply IH, env_rel_cons; [| apply env_rel_cons]; assumption.
  - (* tinl *) sim IH e Henv. constructor. constructor. assumption.
  - (* tinr *) sim IH e Henv. constructor. constructor. assumption.
  - (* tmatch_sum *)
    sim IH e Henv. sim_val; apply IH, env_rel_cons; assumption.
  - (* tbin_op *)
    sim IH a Henv. sim IH b Henv.
    erewrite eval_bin_op_val_rel by eassumption.
    match goal with |- context [eval_bin_op ?o ?x ?y] => destruct (eval_bin_op o x y) end;
      constructor; apply val_rel_refl.
  - (* tif *)
    sim IH c Henv. sim_val.
    match goal with |- context [if ?b then _ else _] => destruct b end;
      apply IH; assumption.
  - (* tdiverge *) constructor.
  - (* tloop *)
    sim IH a Henv.
    apply run_loop_rel; [assumption |].
    intros v v' Hvv'. cbv beta. apply IH, env_rel_cons; assumption.
Qed.

(** *** Shift and variable substitution as renamings *)

(** Insert [k] slots after the first [n] variables. *)
Definition shift_ren (n k : nat) : var -> var :=
  fun x => if lt_dec x n then x else x + k.

Lemma upn_tm_shift_ren : forall n k x,
  upn_tm n (tm_shift k) x = tvar (shift_ren n k x).
Proof.
  intros n k x. rewrite iter_up_tm. unfold shift_ren, tm_shift.
  destruct (lt_dec x n); [reflexivity|]. simpl. f_equal. lia.
Qed.

Lemma subst_tm_shift_ren : forall n k t,
  subst_tm TVar (upn_tm n (tm_shift k)) t = ren_tm id (shift_ren n k) t.
Proof.
  intros. rewrite ren_subst_tm. apply subst_tm_ext.
  - reflexivity.
  - intro x. unfold funcomp. apply upn_tm_shift_ren.
Qed.

(** Replace variable [n] by variable [n + i] (counted in the environment
    without the removed entry) and close the gap above it. *)
Definition subst_ren (n i : nat) : var -> var :=
  fun x => if lt_dec x n then x
           else match x - n with 0 => i + n | S k => k + n end.

Lemma upn_tm_subst_ren : forall n i x,
  upn_tm n (tvar i .: tvar) x = tvar (subst_ren n i x).
Proof.
  intros n i x. rewrite iter_up_tm. unfold subst_ren.
  destruct (lt_dec x n); [reflexivity|].
  destruct (x - n); reflexivity.
Qed.

Lemma subst_tm_subst_ren : forall n i t,
  subst_tm TVar (upn_tm n (tvar i .: tvar)) t = ren_tm id (subst_ren n i) t.
Proof.
  intros. rewrite ren_subst_tm. apply subst_tm_ext.
  - reflexivity.
  - intro x. unfold funcomp. apply upn_tm_subst_ren.
Qed.

(** *** Environment lookups through the two renamings *)

Lemma nth_error_shift_ren : forall (venv1 venv2 venv3 : list Value) x,
  nth_error (venv1 ++ venv3) x =
  nth_error (venv1 ++ venv2 ++ venv3) (shift_ren (length venv1) (length venv2) x).
Proof.
  intros. unfold shift_ren. destruct (lt_dec x (length venv1)).
  - rewrite !nth_error_app1 by lia. reflexivity.
  - rewrite !nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma nth_error_subst_ren : forall (venv_pre : list Value) va venv i,
  nth_error venv i = Some va ->
  forall x,
  nth_error (venv_pre ++ va :: venv) x =
  nth_error (venv_pre ++ venv) (subst_ren (length venv_pre) i x).
Proof.
  intros venv_pre va venv i Hnth x. unfold subst_ren.
  destruct (lt_dec x (length venv_pre)).
  - rewrite !nth_error_app1 by lia. reflexivity.
  - rewrite (nth_error_app2 venv_pre (va :: venv)) by lia.
    destruct (x - length venv_pre) as [|k] eqn:E; simpl;
      rewrite (nth_error_app2 venv_pre venv) by lia.
    + replace (i + length venv_pre - length venv_pre) with i by lia.
      symmetry. exact Hnth.
    + f_equal. lia.
Qed.

(** *** Corollaries *)

(** Weakening (Lemma 3.7), in both orientations. *)
Lemma eval_shift_rel : forall fuel p venv1 venv2 venv3,
  res_rel (eval fuel (venv1 ++ venv3) p)
          (eval fuel (venv1 ++ venv2 ++ venv3)
             (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) p)).
Proof.
  intros. rewrite subst_tm_shift_ren.
  pose proof (eval_ren_rel fuel p id _ id _ (shift_ren (length venv1) (length venv2))
    (env_rel_of_nth_eq _ _ _ _ (nth_error_shift_ren venv1 venv2 venv3))) as H.
  rewrite ren_tm_id in H. exact H.
Qed.

Lemma eval_shift_rel_bwd : forall fuel p venv1 venv2 venv3,
  res_rel (eval fuel (venv1 ++ venv2 ++ venv3)
             (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) p))
          (eval fuel (venv1 ++ venv3) p).
Proof.
  intros. rewrite subst_tm_shift_ren.
  pose proof (eval_ren_rel fuel p id _ (shift_ren (length venv1) (length venv2)) _ id
    (env_rel_of_nth_eq _ _ _ _
      (fun x => eq_sym (nth_error_shift_ren venv1 venv2 venv3 x)))) as H.
  rewrite ren_tm_id in H. exact H.
Qed.

(** Substitution of a variable for an environment entry (§3.6), in both
    orientations. *)
Lemma eval_subst_rel : forall fuel p venv_pre va venv i,
  nth_error venv i = Some va ->
  res_rel (eval fuel (venv_pre ++ va :: venv) p)
          (eval fuel (venv_pre ++ venv)
             (subst_tm TVar (upn_tm (length venv_pre) (tvar i .: tvar)) p)).
Proof.
  intros fuel p venv_pre va venv i Hnth. rewrite subst_tm_subst_ren.
  pose proof (eval_ren_rel fuel p id _ id _ (subst_ren (length venv_pre) i)
    (env_rel_of_nth_eq _ _ _ _ (nth_error_subst_ren venv_pre va venv i Hnth))) as H.
  rewrite ren_tm_id in H. exact H.
Qed.

Lemma eval_subst_rel_bwd : forall fuel p venv_pre va venv i,
  nth_error venv i = Some va ->
  res_rel (eval fuel (venv_pre ++ venv)
             (subst_tm TVar (upn_tm (length venv_pre) (tvar i .: tvar)) p))
          (eval fuel (venv_pre ++ va :: venv) p).
Proof.
  intros fuel p venv_pre va venv i Hnth. rewrite subst_tm_subst_ren.
  pose proof (eval_ren_rel fuel p id _ (subst_ren (length venv_pre) i) _ id
    (env_rel_of_nth_eq _ _ _ _
      (fun x => eq_sym (nth_error_subst_ren venv_pre va venv i Hnth x)))) as H.
  rewrite ren_tm_id in H. exact H.
Qed.

(** ** Evaluation to [true]

    [eval_to_true venv t] holds when every terminating evaluation of [t]
    in [venv] yields [true]; timeouts are allowed. It is the term
    interpretation E⟦t⟧ of Figure 8 at the singleton semantic type
    {true} (see [eval_to_true_semtype] in [Interp]), and it is what the
    interpretation of a refinement type asks of the predicate. *)

Definition eval_to_true (venv: list Value) (t: Term) : Prop :=
  forall fuel r, eval fuel venv t = Some r -> exists v, r = Some v /\ v = vbool true.

(** *** Invariance under type erasure *)

Lemma eval_to_true_erase_eq : forall venv t1 t2,
  erase_ty_in_tm t1 = erase_ty_in_tm t2 ->
  eval_to_true venv t1 <-> eval_to_true venv t2.
Proof.
  intros venv t1 t2 Herase_eq.
  unfold eval_to_true.
  assert (Herase : forall fuel,
    oov_map erase_ty_in_val (eval fuel venv t1) =
    oov_map erase_ty_in_val (eval fuel venv t2)).
  { intro fuel. rewrite eval_erase_ty, eval_erase_ty, Herase_eq. reflexivity. }
  enough (Hdir : forall ta tb,
    (forall fuel, oov_map erase_ty_in_val (eval fuel venv ta) =
                  oov_map erase_ty_in_val (eval fuel venv tb)) ->
    (forall fuel r, eval fuel venv ta = Some r -> exists v, r = Some v /\ v = vbool true) ->
    forall fuel r, eval fuel venv tb = Some r -> exists v, r = Some v /\ v = vbool true).
  { split.
    - apply Hdir. exact Herase.
    - apply Hdir. intro fuel. symmetry. apply Herase. }
  intros ta tb Hab Ha fuel r Heval.
  specialize (Hab fuel). rewrite Heval in Hab.
  destruct (eval fuel venv ta) as [[v'|]|] eqn:Hta; simpl in Hab.
  - destruct r as [v|]; [|discriminate].
    injection Hab as Hab.
    destruct (Ha fuel (Some v') Hta) as [w [Hw1 Hw2]].
    injection Hw1 as <-. subst v'. simpl in Hab.
    exists v. split; [reflexivity|].
    apply erase_ty_in_val_vbool_true. symmetry. exact Hab.
  - destruct (Ha fuel None Hta) as [w [Hw _]]. discriminate.
  - destruct r; discriminate.
Qed.

Lemma eval_to_true_ren_ty : forall venv t xi,
  eval_to_true venv (ren_tm xi id t) <-> eval_to_true venv t.
Proof.
  intros. apply eval_to_true_erase_eq. apply erase_ty_in_tm_ren.
Qed.

Lemma eval_to_true_subst_ty : forall venv t sigma_ty,
  eval_to_true venv (subst_tm sigma_ty tvar t) <-> eval_to_true venv t.
Proof.
  intros. apply eval_to_true_erase_eq. apply erase_ty_in_tm_subst.
Qed.

Lemma eval_to_true_subst_ty_gen : forall venv t sigma_ty sigma_tm,
  (forall n, sigma_tm n = tvar n) ->
  eval_to_true venv (subst_tm sigma_ty sigma_tm t) <-> eval_to_true venv t.
Proof.
  intros venv t sigma_ty sigma_tm Htm.
  apply eval_to_true_erase_eq. apply erase_ty_in_tm_subst_gen. exact Htm.
Qed.

(** *** Transfer along [res_rel]: weakening and substitution *)

Lemma res_rel_true : forall r1 r2,
  res_rel r1 r2 ->
  (forall r, r1 = Some r -> exists v, r = Some v /\ v = vbool true) ->
  forall r, r2 = Some r -> exists v, r = Some v /\ v = vbool true.
Proof.
  intros r1 r2 Hrel H r Hr. destruct Hrel as [| | v1 v2 Hv].
  - discriminate.
  - destruct (H _ eq_refl) as [w [Hw _]]. discriminate.
  - injection Hr as Hr. subst.
    destruct (H _ eq_refl) as [w [Hw Hwt]]. injection Hw as Hw. subst.
    inversion Hv; subst. eauto.
Qed.

Lemma eval_to_true_rel : forall env1 t1 env2 t2,
  (forall fuel, res_rel (eval fuel env1 t1) (eval fuel env2 t2)) ->
  eval_to_true env1 t1 -> eval_to_true env2 t2.
Proof.
  intros env1 t1 env2 t2 Hrel H fuel.
  apply (res_rel_true _ _ (Hrel fuel)). exact (H fuel).
Qed.

(** Weakening (Lemma 3.7). *)
Lemma eval_to_true_shift_env : forall p venv1 venv2 venv3,
  eval_to_true (venv1 ++ venv3) p <->
  eval_to_true (venv1 ++ venv2 ++ venv3)
    (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) p).
Proof.
  intros. split; apply eval_to_true_rel; intro fuel;
    [apply eval_shift_rel | apply eval_shift_rel_bwd].
Qed.

(** Substitution of a variable for an environment entry (§3.6). *)
Lemma eval_to_true_subst_env : forall p venv_prefix va venv i,
  nth_error venv i = Some va ->
  eval_to_true (venv_prefix ++ va :: venv) p <->
  eval_to_true (venv_prefix ++ venv)
    (subst_tm TVar (upn_tm (length venv_prefix) (tvar i .: tvar)) p).
Proof.
  intros. split; apply eval_to_true_rel; intro fuel;
    [apply eval_subst_rel | apply eval_subst_rel_bwd]; assumption.
Qed.
