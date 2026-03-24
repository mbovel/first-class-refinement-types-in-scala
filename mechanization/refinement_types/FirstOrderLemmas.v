(** * Lemmas about First-Order Types *)

From Stdlib Require Import ZArith.BinInt.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Interp.
Require Import RefinementTypes.FirstOrder.

(** Values of first-order types are first-order values. *)
Lemma fo_interp_is_fo_val: forall T tvars venv val,
  fo T = true ->
  interp tvars venv T val ->
  fo_val val.
Proof.
  induction T; intros tvars venv val Hfo Hinterp; simpl in Hfo;
    try discriminate; simpl in Hinterp.
  - (* TUnit *) unfold fo_val. left. exact Hinterp.
  - (* TBool *) unfold fo_val. right; left. exact Hinterp.
  - (* TInt32 *) unfold fo_val. right; right. exact Hinterp.
  - (* TRefine *)
    unfold interp_refine in Hinterp. destruct Hinterp as [HA _].
    eapply IHT; eauto.
Qed.

(** Values of ordered types are int32s, and both args share the same kind. *)
Lemma ordered_interp_pair_compat: forall T tvars venv va vb,
  ordered T = true ->
  interp tvars venv T va ->
  interp tvars venv T vb ->
  exists z1 z2, va = vint32 z1 /\ vb = vint32 z2.
Proof.
  induction T; intros tvars venv va vb Hord Ha Hb; simpl in Hord;
    try discriminate; simpl in Ha, Hb.
  - (* TInt32 *)
    destruct Ha as [z1 Hz1], Hb as [z2 Hz2].
    exists z1, z2. auto.
  - (* TRefine *)
    unfold interp_refine in Ha, Hb. destruct Ha as [Ha _], Hb as [Hb _].
    eapply IHT; eauto.
Qed.

(** Values of boolean types are booleans. *)
Lemma bool_ty_interp_pair_compat: forall T tvars venv va vb,
  bool_ty T = true ->
  interp tvars venv T va ->
  interp tvars venv T vb ->
  exists b1 b2, va = vbool b1 /\ vb = vbool b2.
Proof.
  induction T; intros tvars venv va vb Hbool Ha Hb; simpl in Hbool;
    try discriminate; simpl in Ha, Hb.
  - (* TBool *)
    destruct Ha as [b1 Hb1], Hb as [b2 Hb2].
    exists b1, b2. auto.
  - (* TRefine *)
    unfold interp_refine in Ha, Hb. destruct Ha as [Ha _], Hb as [Hb _].
    eapply IHT; eauto.
Qed.

(** Bridge: type-level bin_op compatibility implies value-level compatibility. *)
Lemma bin_op_ty_interp_val_pair_compat: forall op T tvars venv va vb,
  bin_op_ty_compat op T = true ->
  interp tvars venv T va ->
  interp tvars venv T vb ->
  bin_op_val_pair_compat op va vb.
Proof.
  intros op T tvars venv va vb Hcompat Ha Hb.
  destruct op; simpl in Hcompat; simpl.
  - (* OpEq *) split; eapply fo_interp_is_fo_val; eauto.
  - (* OpNeq *) split; eapply fo_interp_is_fo_val; eauto.
  - (* OpLt *) eapply ordered_interp_pair_compat; eauto.
  - (* OpLe *) eapply ordered_interp_pair_compat; eauto.
  - (* OpGe *) eapply ordered_interp_pair_compat; eauto.
  - (* OpGt *) eapply ordered_interp_pair_compat; eauto.
  - (* OpAnd *) eapply bool_ty_interp_pair_compat; eauto.
  - (* OpOr *) eapply bool_ty_interp_pair_compat; eauto.
  - (* OpAdd *) eapply ordered_interp_pair_compat; eauto.
  - (* OpSub *) eapply ordered_interp_pair_compat; eauto.
  - (* OpMul *) eapply ordered_interp_pair_compat; eauto.
  - (* OpDiv *) eapply ordered_interp_pair_compat; eauto.
  - (* OpMod *) eapply ordered_interp_pair_compat; eauto.
Qed.

(** If an ordered type interprets a vint32 value, its base type is TInt32. *)
Lemma ordered_interp_vint32_base_ty: forall T tvars venv z,
  ordered T = true ->
  interp tvars venv T (vint32 z) ->
  base_ty T = TInt32.
Proof.
  induction T; intros tvars venv z Hord Hinterp; simpl in Hord;
    try discriminate; simpl.
  - (* TInt32 *) reflexivity.
  - (* TRefine *)
    simpl in Hinterp. unfold interp_refine in Hinterp.
    destruct Hinterp as [HA _].
    eapply IHT; eauto.
Qed.

(** The result of eval_bin_op is in the interpretation of the result type. *)
Lemma eval_bin_op_result_in_interp: forall op T tvars venv va vb v,
  bin_op_ty_compat op T = true ->
  interp tvars venv T va ->
  interp tvars venv T vb ->
  eval_bin_op op va vb = Some v ->
  interp tvars venv (bin_op_result_ty op T) v.
Proof.
  intros op T tvars venv va vb v Hcompat Ha Hb Heval.
  destruct op; simpl in Hcompat; simpl.
  (* Comparison ops -> TBool result *)
  all: try (
    pose proof (fo_interp_is_fo_val T tvars venv va Hcompat Ha) as Hfoa;
    pose proof (fo_interp_is_fo_val T tvars venv vb Hcompat Hb) as Hfob;
    unfold fo_val in Hfoa, Hfob;
    destruct Hfoa as [-> | [[b1 ->] | [z1 ->]]];
    destruct Hfob as [-> | [[b2 ->] | [z2 ->]]];
    simpl in Heval; inversion Heval; subst;
    simpl; eauto; fail).
  all: try (
    destruct (ordered_interp_pair_compat T tvars venv va vb Hcompat Ha Hb)
      as [z1 [z2 [-> ->]]];
    simpl in Heval; inversion Heval; subst;
    simpl; eauto; fail).
  all: try (
    destruct (bool_ty_interp_pair_compat T tvars venv va vb Hcompat Ha Hb)
      as [b1 [b2 [-> ->]]];
    simpl in Heval; inversion Heval; subst;
    simpl; eauto; fail).
  (* Arithmetic ops -> base_ty T result *)
  all: (
    destruct (ordered_interp_pair_compat T tvars venv va vb Hcompat Ha Hb)
      as [z1 [z2 [-> ->]]];
    simpl in Heval; inversion Heval; subst;
    rewrite (ordered_interp_vint32_base_ty T tvars venv z1 Hcompat Ha);
    simpl; eauto).
Qed.
