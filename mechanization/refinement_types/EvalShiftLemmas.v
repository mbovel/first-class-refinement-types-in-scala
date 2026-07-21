(** * Evaluation Weakening (Lemma 3.7)

    Weakening for the evaluator: inserting values in the middle of the
    environment (with the matching de Bruijn shift on the term) preserves
    evaluation results. Results are not preserved exactly, because closures
    capture the extended environment; they are preserved up to the
    compatibility relation [res_weaken_compat] (written ≈ in the paper),
    which relates first-order values to themselves and closures to closures
    with correspondingly extended captured environments. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.

Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Tactics.
Require Import RefinementTypes.ListLemmas.

(** ** Weakening compatibility relation *)

Inductive val_weaken_compat : Value -> Value -> Prop :=
| vc_unit :
    val_weaken_compat vunit vunit
| vc_bool : forall b,
    val_weaken_compat (vbool b) (vbool b)
| vc_int32 : forall z,
    val_weaken_compat (vint32 z) (vint32 z)
| vc_pair : forall v1 v1' v2 v2',
    val_weaken_compat v1 v1' ->
    val_weaken_compat v2 v2' ->
    val_weaken_compat (vpair v1 v2) (vpair v1' v2')
| vc_inl : forall v1 v2,
    val_weaken_compat v1 v2 ->
    val_weaken_compat (vinl v1) (vinl v2)
| vc_inr : forall v1 v2,
    val_weaken_compat v1 v2 ->
    val_weaken_compat (vinr v1) (vinr v2)
| vc_abs : forall venv1 venv1' venv2 venv2' venv3 venv3' body,
    Forall2 val_weaken_compat venv1 venv1' ->
    Forall2 val_weaken_compat venv3 venv3' ->
    val_weaken_compat
      (vabs (venv1 ++ venv2 ++ venv3) (subst_tm TVar (up_tm_tm (upn_tm (length venv1) (tm_shift (length venv2)))) body))
      (vabs (venv1' ++ venv2' ++ venv3') (subst_tm TVar (up_tm_tm (upn_tm (length venv1') (tm_shift (length venv2')))) body))
| vc_tabs : forall venv1 venv1' venv2 venv2' venv3 venv3' body,
    Forall2 val_weaken_compat venv1 venv1' ->
    Forall2 val_weaken_compat venv3 venv3' ->
    val_weaken_compat
      (vtabs (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) body))
      (vtabs (venv1' ++ venv2' ++ venv3') (subst_tm TVar (upn_tm (length venv1') (tm_shift (length venv2'))) body)).

Lemma val_weaken_compat_refl: forall v,
  val_weaken_compat v v.
Proof.
  induction v as [| b | z | v1 v2 IH1 IH2 | v IH | v IH | venv body IH | venv body IH] using Value_ind_nested.
  - apply vc_unit.
  - apply vc_bool.
  - apply vc_int32.
  - apply vc_pair; assumption.
  - apply vc_inl; assumption.
  - apply vc_inr; assumption.
  - replace (vabs venv body) with
      (vabs ([] ++ [] ++ venv) (subst_tm TVar (up_tm_tm (upn_tm (length (@nil Value)) (tm_shift (length (@nil Value))))) body)).
    + apply vc_abs; [constructor | apply (Forall_Forall2_refl _ _ IH)].
    + simpl. f_equal. etransitivity; [apply subst_tm_ext; [reflexivity | exact up_tm_tm_shift0_id] |].
      apply subst_tm_id.
  - replace (vtabs venv body) with
      (vtabs ([] ++ [] ++ venv) (subst_tm TVar (upn_tm (length (@nil Value)) (tm_shift (length (@nil Value)))) body)).
    + apply vc_tabs; [constructor | apply (Forall_Forall2_refl _ _ IH)].
    + simpl. f_equal. etransitivity; [apply subst_tm_ext; [reflexivity | exact tm_shift_0_eq] |].
      apply subst_tm_id.
Qed.

Inductive res_weaken_compat : (option (option Value)) -> (option (option Value)) -> Prop :=
| rc_none :
    res_weaken_compat None None
| rc_some_none :
    res_weaken_compat (Some None) (Some None)
| rc_some_some : forall v1 v2,
    val_weaken_compat v1 v2 ->
    res_weaken_compat (Some (Some v1)) (Some (Some v2)).

Lemma res_weaken_compat_refl: forall r,
  res_weaken_compat r r.
Proof.
  intros [ [v|] | ]; constructor; auto using val_weaken_compat_refl.
Qed.

Lemma eval_bin_op_val_weaken_compat: forall op va va' vb vb',
  val_weaken_compat va va' ->
  val_weaken_compat vb vb' ->
  eval_bin_op op va vb = eval_bin_op op va' vb'.
Proof.
  intros op va va' vb vb' Hva Hvb.
  destruct va; inversion Hva; subst;
  destruct vb; inversion Hvb; subst;
  destruct op; try reflexivity.
Qed.

Lemma run_loop_weaken_compat : forall step1 step2 n va va' r,
  val_weaken_compat va va' ->
  (forall v v', val_weaken_compat v v' ->
    forall r, step1 v = r ->
    exists r', res_weaken_compat r r' /\ step2 v' = r') ->
  run_loop step1 n va = r ->
  exists r', res_weaken_compat r r' /\ run_loop step2 n va' = r'.
Proof.
  intros step1 step2 n.
  induction n; intros va va' r Hvca Hstep Hloop.
  - simpl in *. subst. exists None. split; [constructor | reflexivity].
  - simpl in *.
    destruct (step1 va) as [[v|]|] eqn:Hs1.
    + destruct (Hstep va va' Hvca _ Hs1) as [[[v'|]|] [Hrc1 Hs2]];
        [| inversion Hrc1 | inversion Hrc1].
      inversion Hrc1 as [| | ? ? Hvcv]; subst.
      rewrite Hs2.
      destruct v as [| bv | zv | v1v v2v | vinlv | vinrv | envv bodyv | envv bodyv];
        inversion Hvcv; subst.
      (* vinl - continue *)
      5: { eapply IHn; eauto. }
      (* vinr - break *)
      5: { eexists; split; [constructor; eauto | reflexivity]. }
      (* stuck cases: vunit, vbool, vint32, vpair, vabs, vtabs *)
      all: (subst; eexists; split; [constructor | reflexivity]).
    + destruct (Hstep va va' Hvca _ Hs1) as [[[?|]|] [Hrc1 Hs2]];
        [inversion Hrc1 | | inversion Hrc1].
      rewrite Hs2. subst. eexists; split; [constructor | reflexivity].
    + destruct (Hstep va va' Hvca _ Hs1) as [[[?|]|] [Hrc1 Hs2]];
        [inversion Hrc1 | inversion Hrc1 |].
      rewrite Hs2. subst. eexists; split; [constructor | reflexivity].
Qed.

(** ** Weakening simulation (Lemma 3.7) *)

Lemma eval_weaken_compat: forall fuel t venv1 venv1' venv2 venv2' venv3 venv3' r,
  Forall2 val_weaken_compat venv1 venv1' ->
  Forall2 val_weaken_compat venv3 venv3' ->
  eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) t) = r ->
  exists r',
    res_weaken_compat r r' /\
    eval fuel (venv1' ++ venv2' ++ venv3') (subst_tm TVar (upn_tm (length venv1') (tm_shift (length venv2'))) t) = r'.
Proof.
    induction fuel; intros t venv1 venv1' venv2 venv2' venv3 venv3' r Hvenv1 Hvenv3 Heval.
    { (* fuel = 0: timeout *)
      simpl in Heval. subst. exists None. split; [constructor | reflexivity]. }
    destruct t as [|b|z|x|A body|f a|L U body|f A|A a body|e1 e2|e body|Binl einl|Ainr einr|e bl br|b0 a b|a b1 b2| |a body]; simpl in *.
    + (* tunit *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tbool *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tint32 *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tvar *)
      rewrite iter_up_tm in Heval.
      pose proof (Forall2_length Hvenv1) as Hlen1.
      pose proof (Forall2_length Hvenv3) as Hlen3.
      destruct (lt_dec x (length venv1)) as [Hlt|Hge]; simpl in Heval.
      * rewrite nth_error_app1 in Heval by lia.
        destruct (nth_error venv1 x) as [v|] eqn:Hnth1.
        -- subst.
           destruct (Forall2_exists2 _ _ _ _ _ Hvenv1 Hnth1) as [v2 [Hnth2 Hvc]].
           exists (Some (Some v2)). split; [constructor; assumption |].
           rewrite iter_up_tm. destruct (lt_dec x (length venv1')) as [_|Habs]; [|lia].
           simpl. rewrite nth_error_app1 by lia. rewrite Hnth2. reflexivity.
        -- (* nth_error venv1 = None, but x < length venv1 — impossible *)
           apply nth_error_None in Hnth1. lia.
      * rewrite !nth_error_app2 in Heval by lia.
        replace (x - length venv1 + length venv2 + length venv1 - length venv1 - length venv2)
          with (x - length venv1) in Heval by lia.
        destruct (nth_error venv3 (x - length venv1)) as [v|] eqn:Hnth1.
        -- subst.
           destruct (Forall2_exists2 _ _ _ _ _ Hvenv3 Hnth1) as [v2 [Hnth2 Hvc]].
           exists (Some (Some v2)). split; [constructor; assumption |].
           rewrite iter_up_tm. destruct (lt_dec x (length venv1')) as [Habs|_]; [lia|].
           simpl. rewrite !nth_error_app2 by lia.
           replace (x - length venv1' + length venv2' + length venv1' - length venv1' - length venv2')
             with (x - length venv1') by lia.
           replace (x - length venv1') with (x - length venv1) by lia.
           rewrite Hnth2. reflexivity.
        -- (* nth_error venv3 = None: stuck on both sides *)
           subst.
           exists (Some None). split; [constructor |].
           rewrite iter_up_tm. destruct (lt_dec x (length venv1')) as [Habs|_]; [lia|].
           simpl. rewrite !nth_error_app2 by lia.
           replace (x - length venv1' + length venv2' + length venv1' - length venv1' - length venv2')
             with (x - length venv1') by lia.
           replace (x - length venv1') with (x - length venv1) by lia.
           apply nth_error_None in Hnth1.
           assert (nth_error venv3' (x - length venv1) = None) as -> by (apply nth_error_None; lia).
           reflexivity.
    + (* tabs *)
      subst. rewrite !subst_tm_up_tm_ty_TVar in *.
      eexists; split; [constructor; eapply vc_abs; eassumption | reflexivity].
    + (* tapp f a *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) f)) as [[vf|]|] eqn:Hf1.
      * (* f -> Some (Some vf) *)
        destruct (IHfuel f venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hf1)
          as [[[vf'|]|] [Hrcf Hf2]]; [| inversion Hrcf | inversion Hrcf].
        inversion Hrcf as [| | ? ? Hvcf]; subst.
        destruct vf as [| bf | zf | v1f v2f | vinlf | vinrf | envf bodyf | envf bodyf];
          try (inversion Hvcf; subst; rewrite Hf2; simpl; eexists; split; [constructor | reflexivity]).
        (* vf = vabs envf bodyf *)
        inversion Hvcf as [| | | | | | ef1 ef1' ef2 ef2' ef3 ef3' bdy Hef1 Hef3 Hvabs1 Hvabs2| ]; subst.
        rewrite Hf2. simpl.
        destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) a)) as [[va|]|] eqn:Ha1.
        -- (* a -> Some (Some va) *)
           destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
             as [[[va'|]|] [Hrca Ha2]]; [| inversion Hrca | inversion Hrca].
           inversion Hrca as [| | ? ? Hvca]; subst.
           rewrite Ha2. simpl.
           eapply (IHfuel bdy (va :: ef1) (va' :: ef1') ef2 ef2' ef3 ef3'); auto.
        -- (* a -> Some None *)
           destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
             as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | | inversion Hrca].
           rewrite Ha2. eexists; split; [constructor | reflexivity].
        -- (* a -> None *)
           destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
             as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | inversion Hrca |].
           rewrite Ha2. eexists; split; [constructor | reflexivity].
      * (* f -> Some None *)
        subst.
        destruct (IHfuel f venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hf1)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | | inversion Hrcf].
        rewrite Hf2. simpl. eexists; split; [constructor | reflexivity].
      * (* f -> None *)
        subst.
        destruct (IHfuel f venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hf1)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | inversion Hrcf |].
        rewrite Hf2. eexists; split; [constructor | reflexivity].
    + (* ttabs *)
      subst. rewrite !subst_tm_up_ty_TVar_shift in *.
      eexists; split; [constructor; eapply vc_tabs; eassumption | reflexivity].
    + (* ttapp f A *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) f)) as [[vf|]|] eqn:Hf1.
      * (* f -> Some (Some vf) *)
        destruct (IHfuel f venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hf1)
          as [[[vf'|]|] [Hrcf Hf2]]; [| inversion Hrcf | inversion Hrcf].
        inversion Hrcf as [| | ? ? Hvcf]; subst.
        destruct vf as [| bf | zf | v1f v2f | vinlf | vinrf | envf bodyf | envf bodyf];
          try (inversion Hvcf; subst; rewrite Hf2; simpl; eexists; split; [constructor | reflexivity]).
        (* vf = vtabs envf bodyf *)
        inversion Hvcf as [| | | | | | | ef1 ef1' ef2 ef2' ef3 ef3' bdy Hef1 Hef3 Hvabs1 Hvabs2]; subst.
        rewrite Hf2. simpl.
        eapply (IHfuel bdy ef1 ef1' ef2 ef2' ef3 ef3'); auto.
      * (* f -> Some None *)
        subst.
        destruct (IHfuel f venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hf1)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | | inversion Hrcf].
        rewrite Hf2. simpl. eexists; split; [constructor | reflexivity].
      * (* f -> None *)
        subst.
        destruct (IHfuel f venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hf1)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | inversion Hrcf |].
        rewrite Hf2. eexists; split; [constructor | reflexivity].
    + (* tlet A a body *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) a)) as [[ve|]|] eqn:He1.
      * (* e -> Some (Some ve) *)
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[ve'|]|] [Hrce He2]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He2. simpl.
        eapply (IHfuel body (ve :: venv1) (ve' :: venv1') venv2 venv2' venv3 venv3'); auto.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | | inversion Hrce].
        rewrite He2. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | inversion Hrce |].
        rewrite He2. eexists; split; [constructor | reflexivity].
    + (* tpair e1 e2 *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) e1)) as [[v1_0|]|] eqn:He1.
      * (* e1 -> Some (Some v1_0) *)
        destruct (IHfuel e1 venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[v1'|]|] [Hrc1 He1']]; [| inversion Hrc1 | inversion Hrc1].
        inversion Hrc1 as [| | ? ? Hvc1]; subst.
        destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) e2)) as [[v2_0|]|] eqn:He2.
        -- (* e2 -> Some (Some v2_0) *)
           destruct (IHfuel e2 venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He2)
             as [[[v2'|]|] [Hrc2 He2']]; [| inversion Hrc2 | inversion Hrc2].
           inversion Hrc2 as [| | ? ? Hvc2]; subst.
           rewrite He1', He2'.
           eexists; split; [constructor; eapply vc_pair; eassumption | reflexivity].
        -- (* e2 -> Some None *)
           destruct (IHfuel e2 venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He2)
             as [[[?|]|] [Hrc2 He2']]; [inversion Hrc2 | | inversion Hrc2].
           subst. rewrite He1', He2'. eexists; split; [constructor | reflexivity].
        -- (* e2 -> None *)
           destruct (IHfuel e2 venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He2)
             as [[[?|]|] [Hrc2 He2']]; [inversion Hrc2 | inversion Hrc2 |].
           subst. rewrite He1', He2'. eexists; split; [constructor | reflexivity].
      * (* e1 -> Some None *)
        subst.
        destruct (IHfuel e1 venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrc1 He1']]; [inversion Hrc1 | | inversion Hrc1].
        rewrite He1'. eexists; split; [constructor | reflexivity].
      * (* e1 -> None *)
        subst.
        destruct (IHfuel e1 venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrc1 He1']]; [inversion Hrc1 | inversion Hrc1 |].
        rewrite He1'. eexists; split; [constructor | reflexivity].
    + (* tmatch_pair e body *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) e)) as [[ve|]|] eqn:He.
      * (* e -> Some (Some ve) *)
        destruct (IHfuel e venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He)
          as [[[ve'|]|] [Hrce He']]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        destruct ve as [| be | ze | v1_0 v2_0 | vinle | vinre | enve bodye | enve bodye];
          try (inversion Hvce; subst; rewrite He'; simpl; eexists; split; [constructor | reflexivity]).
        (* ve = vpair v1_0 v2_0 *)
        inversion Hvce; subst.
        rewrite He'. simpl.
        eapply (IHfuel body (v2_0 :: v1_0 :: venv1) (v2' :: v1' :: venv1') venv2 venv2' venv3 venv3'); auto.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | | inversion Hrce].
        rewrite He'. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | inversion Hrce |].
        rewrite He'. eexists; split; [constructor | reflexivity].
    + (* tinl *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) einl)) as [[ve|]|] eqn:He1.
      * destruct (IHfuel einl venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[ve'|]|] [Hrce He2]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He2. eexists; split; [constructor; apply vc_inl; eauto | reflexivity].
      * subst.
        destruct (IHfuel einl venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | | inversion Hrce].
        rewrite He2. eexists; split; [constructor | reflexivity].
      * subst.
        destruct (IHfuel einl venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | inversion Hrce |].
        rewrite He2. eexists; split; [constructor | reflexivity].
    + (* tinr *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) einr)) as [[ve|]|] eqn:He1.
      * destruct (IHfuel einr venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[ve'|]|] [Hrce He2]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He2. eexists; split; [constructor; apply vc_inr; eauto | reflexivity].
      * subst.
        destruct (IHfuel einr venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | | inversion Hrce].
        rewrite He2. eexists; split; [constructor | reflexivity].
      * subst.
        destruct (IHfuel einr venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He1)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | inversion Hrce |].
        rewrite He2. eexists; split; [constructor | reflexivity].
    + (* tmatch_sum *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) e)) as [[ve|]|] eqn:He.
      * (* e -> Some (Some ve) *)
        destruct (IHfuel e venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He)
          as [[[ve'|]|] [Hrce He']]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        destruct ve as [| be | ze | v1_0 v2_0 | vinle | vinre | enve bodye | enve bodye];
          try (inversion Hvce; subst; rewrite He'; simpl; eexists; split; [constructor | reflexivity]).
        (* ve = vinl *)
        -- inversion Hvce; subst.
           rewrite He'. simpl.
           eapply (IHfuel bl (vinle :: venv1) (v2 :: venv1') venv2 venv2' venv3 venv3'); auto.
        (* ve = vinr *)
        -- inversion Hvce; subst.
           rewrite He'. simpl.
           eapply (IHfuel br (vinre :: venv1) (v2 :: venv1') venv2 venv2' venv3 venv3'); auto.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | | inversion Hrce].
        rewrite He'. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | inversion Hrce |].
        rewrite He'. eexists; split; [constructor | reflexivity].
    + (* tbin_op op a b *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) a)) as [[va0|]|] eqn:Ha1.
      * (* a -> Some (Some va0) *)
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
          as [[[va'|]|] [Hrca Ha2]]; [| inversion Hrca | inversion Hrca].
        inversion Hrca as [| | ? ? Hvca]; subst.
        destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) b)) as [[vb0|]|] eqn:Hb1.
        -- (* b -> Some (Some vb0) *)
           destruct (IHfuel b venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hb1)
             as [[[vb'|]|] [Hrcb Hb2]]; [| inversion Hrcb | inversion Hrcb].
           inversion Hrcb as [| | ? ? Hvcb]; subst.
           rewrite Ha2, Hb2.
           rewrite <- (eval_bin_op_val_weaken_compat b0 _ _ _ _ Hvca Hvcb).
           destruct (eval_bin_op b0 va0 vb0).
           ++ eexists; split; [constructor; apply val_weaken_compat_refl | reflexivity].
           ++ eexists; split; [constructor | reflexivity].
        -- (* b -> Some None *)
           destruct (IHfuel b venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hb1)
             as [[[?|]|] [Hrcb Hb2]]; [inversion Hrcb | | inversion Hrcb].
           subst. rewrite Ha2, Hb2. eexists; split; [constructor | reflexivity].
        -- (* b -> None *)
           destruct (IHfuel b venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hb1)
             as [[[?|]|] [Hrcb Hb2]]; [inversion Hrcb | inversion Hrcb |].
           subst. rewrite Ha2, Hb2. eexists; split; [constructor | reflexivity].
      * (* a -> Some None *)
        subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | | inversion Hrca].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
      * (* a -> None *)
        subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | inversion Hrca |].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
    + (* tif a b1 b2 *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) a)) as [[vc|]|] eqn:Hc1.
      * (* cond -> Some (Some vc) *)
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hc1)
          as [[[vc'|]|] [Hrcc Hc2]]; [| inversion Hrcc | inversion Hrcc].
        inversion Hrcc as [| | ? ? Hvcc]; subst.
        destruct vc as [| [] | zc | v1c v2c | vinlc | vinrc | envc bodyc | envc bodyc];
          inversion Hvcc; subst; rewrite Hc2; simpl;
          try (eexists; split; [constructor | reflexivity]).
        -- (* true *) eapply IHfuel; eauto.
        -- (* false *) eapply IHfuel; eauto.
      * (* cond -> Some None *)
        subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hc1)
          as [[[?|]|] [Hrcc Hc2]]; [inversion Hrcc | | inversion Hrcc].
        rewrite Hc2. eexists; split; [constructor | reflexivity].
      * (* cond -> None *)
        subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Hc1)
          as [[[?|]|] [Hrcc Hc2]]; [inversion Hrcc | inversion Hrcc |].
        rewrite Hc2. eexists; split; [constructor | reflexivity].
    + (* tdiverge *) subst. eexists; split; [constructor | reflexivity].
    + (* tloop *)
      destruct (eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) a)) as [[va0|]|] eqn:Ha1.
      * destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
          as [[[va'|]|] [Hrca Ha2]]; [| inversion Hrca | inversion Hrca].
        inversion Hrca as [| | ? ? Hvca]; subst.
        rewrite Ha2.
        eapply run_loop_weaken_compat; eauto.
        intros v v' Hvcv r0 Hr0.
        eapply (IHfuel body (v :: venv1) (v' :: venv1') venv2 venv2' venv3 venv3');
          auto.
      * subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | | inversion Hrca].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
      * subst.
        destruct (IHfuel a venv1 venv1' venv2 venv2' venv3 venv3' _ Hvenv1 Hvenv3 Ha1)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | inversion Hrca |].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
Qed.

(** ** Corollaries: shifting the environment *)

(** Forward: small env result implies big env result (with res_weaken_compat). *)
Lemma eval_shift_env_fwd: forall fuel p venv1 venv2 venv3 r,
  eval fuel (venv1 ++ venv3) p = r ->
  exists r', res_weaken_compat r r' /\
    eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) p) = r'.
Proof.
  intros.
  edestruct (eval_weaken_compat fuel p venv1 venv1 [] venv2 venv3 venv3 r) as [r' [Hrc Hr']].
  - apply Forall2_refl. intro. apply val_weaken_compat_refl.
  - apply Forall2_refl. intro. apply val_weaken_compat_refl.
  - simpl. rewrite subst_tm_upn_shift0. exact H.
  - eauto.
Qed.

(** Backward: big env result implies small env result (with res_weaken_compat). *)
Lemma eval_shift_env_bwd: forall fuel p venv1 venv2 venv3 r,
  eval fuel (venv1 ++ venv2 ++ venv3) (subst_tm TVar (upn_tm (length venv1) (tm_shift (length venv2))) p) = r ->
  exists r', res_weaken_compat r r' /\
    eval fuel (venv1 ++ venv3) p = r'.
Proof.
  intros.
  edestruct (eval_weaken_compat fuel p venv1 venv1 venv2 [] venv3 venv3 r) as [r' [Hrc Hr']].
  - apply Forall2_refl. intro. apply val_weaken_compat_refl.
  - apply Forall2_refl. intro. apply val_weaken_compat_refl.
  - exact H.
  - simpl in Hr'. rewrite subst_tm_upn_shift0 in Hr'. eauto.
Qed.
