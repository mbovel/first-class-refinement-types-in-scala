(** * Evaluation Substitution (§3.6)

    Substitution analogue of evaluation weakening (Lemma 3.7): replacing an
    environment entry by a variable reference (substituting [tvar i] for the
    removed binding) preserves evaluation results, up to the corresponding
    substitution compatibility relation [res_subst_compat]. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Eval.
Require Import RefinementTypes.Tactics.
Require Import RefinementTypes.ListLemmas.

(** ** Substitution compatibility relation *)

Inductive val_subst_compat : Value -> Value -> Prop :=
| vsc_unit : val_subst_compat vunit vunit
| vsc_bool : forall b, val_subst_compat (vbool b) (vbool b)
| vsc_int32 : forall z, val_subst_compat (vint32 z) (vint32 z)
| vsc_pair : forall v1 v1' v2 v2',
    val_subst_compat v1 v1' ->
    val_subst_compat v2 v2' ->
    val_subst_compat (vpair v1 v2) (vpair v1' v2')
| vsc_inl : forall v1 v2,
    val_subst_compat v1 v2 ->
    val_subst_compat (vinl v1) (vinl v2)
| vsc_inr : forall v1 v2,
    val_subst_compat v1 v2 ->
    val_subst_compat (vinr v1) (vinr v2)
| vsc_abs : forall env1 env2 body sigma,
    env_subst_compat env1 env2 sigma ->
    val_subst_compat (vabs env1 body) (vabs env2 (subst_tm TVar (up_tm_tm sigma) body))
| vsc_tabs : forall env1 env2 body sigma,
    env_subst_compat env1 env2 sigma ->
    val_subst_compat (vtabs env1 body) (vtabs env2 (subst_tm TVar sigma body))
with env_subst_compat : list Value -> list Value -> (var -> Term) -> Prop :=
| esc_id : forall env1 env2,
    Forall2 val_subst_compat env1 env2 ->
    env_subst_compat env1 env2 tvar
| esc_subst : forall venv_pre venv_pre' venv venv' i va va',
    Forall2 val_subst_compat venv_pre venv_pre' ->
    Forall2 val_subst_compat venv venv' ->
    nth_error venv i = Some va ->
    nth_error venv' i = Some va' ->
    val_subst_compat va va' ->
    env_subst_compat
      (venv_pre ++ va :: venv)
      (venv_pre' ++ venv')
      (upn_tm (length venv_pre') (tvar i .: tvar)).

Lemma val_subst_compat_refl: forall v,
  val_subst_compat v v.
Proof.
  induction v as [| b | z | v1 v2 IH1 IH2 | v IH | v IH | venv body IH | venv body IH] using Value_ind_nested.
  - apply vsc_unit.
  - apply vsc_bool.
  - apply vsc_int32.
  - apply vsc_pair; assumption.
  - apply vsc_inl; assumption.
  - apply vsc_inr; assumption.
  - replace body with (subst_tm TVar (up_tm_tm tvar) body) at 2.
    + apply vsc_abs, esc_id, (Forall_Forall2_refl _ _ IH).
    + etransitivity; [apply subst_tm_ext; [reflexivity | apply up_tm_tm_id] |].
      apply subst_tm_id.
  - replace body with (subst_tm TVar tvar body) at 2 by (apply subst_tm_id).
    apply vsc_tabs, esc_id, (Forall_Forall2_refl _ _ IH).
Qed.

Inductive res_subst_compat : (option (option Value)) -> (option (option Value)) -> Prop :=
| rsc_none : res_subst_compat None None
| rsc_some_none : res_subst_compat (Some None) (Some None)
| rsc_some_some : forall v1 v2,
    val_subst_compat v1 v2 ->
    res_subst_compat (Some (Some v1)) (Some (Some v2)).

Lemma res_subst_compat_refl: forall r,
  res_subst_compat r r.
Proof.
  intros [ [v|] | ]; constructor; auto using val_subst_compat_refl.
Qed.

Lemma eval_bin_op_val_subst_compat: forall op va va' vb vb',
  val_subst_compat va va' ->
  val_subst_compat vb vb' ->
  eval_bin_op op va vb = eval_bin_op op va' vb'.
Proof.
  intros op va va' vb vb' Hva Hvb.
  destruct va; inversion Hva; subst;
  destruct vb; inversion Hvb; subst;
  destruct op; try reflexivity.
Qed.

Lemma env_subst_compat_cons: forall v v' env1 env2 sigma,
  val_subst_compat v v' ->
  env_subst_compat env1 env2 sigma ->
  env_subst_compat (v :: env1) (v' :: env2) (up_tm_tm sigma).
Proof.
  intros v v' env1 env2 sigma Hv Hesc.
  inversion Hesc; subst.
  - assert (Heq : up_tm_tm tvar = tvar)
      by (apply functional_extensionality; apply up_tm_tm_id).
    rewrite Heq. apply esc_id. constructor; auto.
  - change (v :: venv_pre ++ va :: venv) with ((v :: venv_pre) ++ va :: venv).
    change (v' :: venv_pre' ++ venv') with ((v' :: venv_pre') ++ venv').
    change (up_tm_tm (upn_tm (length venv_pre') (tvar i .: tvar)))
      with (upn_tm (length (v' :: venv_pre')) (tvar i .: tvar)).
    eapply esc_subst; try eassumption. constructor; assumption.
Qed.

Lemma run_loop_subst_compat_fwd : forall step1 step2 n va va' r,
  val_subst_compat va va' ->
  (forall v v', val_subst_compat v v' ->
    forall r, step1 v = r ->
    exists r', res_subst_compat r r' /\ step2 v' = r') ->
  run_loop step1 n va = r ->
  exists r', res_subst_compat r r' /\ run_loop step2 n va' = r'.
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
      destruct v as [| bv | zv | v1v v2v | v0 | v0 | envv bodyv | envv bodyv];
        inversion Hvcv; subst.
      (* vinl - continue *)
      5: { eapply IHn; eauto. }
      (* vinr - break *)
      5: { eexists; split; [constructor; eauto | reflexivity]. }
      (* stuck cases *)
      all: (subst; eexists; split; [constructor | reflexivity]).
    + destruct (Hstep va va' Hvca _ Hs1) as [[[?|]|] [Hrc1 Hs2]];
        [inversion Hrc1 | | inversion Hrc1].
      rewrite Hs2. subst. eexists; split; [constructor | reflexivity].
    + destruct (Hstep va va' Hvca _ Hs1) as [[[?|]|] [Hrc1 Hs2]];
        [inversion Hrc1 | inversion Hrc1 |].
      rewrite Hs2. subst. eexists; split; [constructor | reflexivity].
Qed.

Lemma run_loop_subst_compat_bwd : forall step1 step2 n va va' r,
  val_subst_compat va va' ->
  (forall v v', val_subst_compat v v' ->
    forall r, step2 v' = r ->
    exists r', res_subst_compat r' r /\ step1 v = r') ->
  run_loop step2 n va' = r ->
  exists r', res_subst_compat r' r /\ run_loop step1 n va = r'.
Proof.
  intros step1 step2 n.
  induction n; intros va va' r Hvca Hstep Hloop.
  - simpl in *. subst. exists None. split; [constructor | reflexivity].
  - simpl in *.
    destruct (step2 va') as [[v'|]|] eqn:Hs2.
    + destruct (Hstep va va' Hvca _ Hs2) as [[[v|]|] [Hrc1 Hs1]];
        [| inversion Hrc1 | inversion Hrc1].
      inversion Hrc1 as [| | ? ? Hvcv]; subst.
      rewrite Hs1.
      destruct v as [| bv | zv | v1v v2v | v0 | v0 | envv bodyv | envv bodyv];
        inversion Hvcv; subst.
      (* vinl - continue *)
      5: { eapply IHn; eauto. }
      (* vinr - break *)
      5: { eexists; split; [constructor; eauto | reflexivity]. }
      (* stuck cases *)
      all: (subst; eexists; split; [constructor | reflexivity]).
    + destruct (Hstep va va' Hvca _ Hs2) as [[[?|]|] [Hrc1 Hs1]];
        [inversion Hrc1 | | inversion Hrc1].
      rewrite Hs1. subst. eexists; split; [constructor | reflexivity].
    + destruct (Hstep va va' Hvca _ Hs2) as [[[?|]|] [Hrc1 Hs1]];
        [inversion Hrc1 | inversion Hrc1 |].
      rewrite Hs1. subst. eexists; split; [constructor | reflexivity].
Qed.

(** ** Substitution simulation *)

Lemma eval_term_subst_compat_fwd: forall fuel t env1 env2 sigma r,
  env_subst_compat env1 env2 sigma ->
  eval fuel env1 t = r ->
  exists r',
    res_subst_compat r r' /\
    eval fuel env2 (subst_tm TVar sigma t) = r'.
Proof.
    induction fuel; intros t env1 env2 sigma r Hesc Heval.
    { simpl in Heval. subst. exists None. split; [constructor | reflexivity]. }
    destruct t as [|b|z|x|A body|f a|L U body|f A|A e body|e1 e2|e body|Binl el|Ainr er|e bl br|b0 a b|c thn els| |a body]; simpl in *.
    + (* tunit *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tbool *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tint32 *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tvar x *)
      inversion Hesc; subst.
      * (* esc_id case *)
        simpl.
        destruct (nth_error env1 x) as [v|] eqn:Hnth1.
        -- subst.
           destruct (Forall2_exists2 _ _ _ _ _ H Hnth1) as [v2 [Hnth2 Hvc]].
           exists (Some (Some v2)). simpl. rewrite Hnth2. split; [constructor; assumption | reflexivity].
        -- subst.
           exists (Some None). simpl.
           apply Forall2_length in H.
           rewrite nth_error_None in Hnth1.
           assert (nth_error env2 x = None) as -> by (apply nth_error_None; lia).
           split; [constructor | reflexivity].
      * (* esc_subst case *)
        pose proof (Forall2_length H) as Hlen.
        destruct (nth_error (venv_pre ++ va :: venv) x) as [v|] eqn:Hnth.
        -- subst. rewrite iter_up_tm.
           destruct (lt_dec x (length venv_pre')).
           ++ simpl. rewrite nth_error_app1 in Hnth by lia.
              destruct (Forall2_exists2 _ _ _ _ _ H Hnth) as [v2 [Hnth' Hvc]].
              exists (Some (Some v2)). split; [constructor; assumption|].
              rewrite nth_error_app1 by lia. rewrite Hnth'. reflexivity.
           ++ destruct (Nat.eq_dec x (length venv_pre')) as [Heq|Hne].
              ** subst x. rewrite !nth_error_app2 in Hnth by lia. rewrite Hlen, Nat.sub_diag in Hnth.
                 simpl in Hnth. injection Hnth as ->. exists (Some (Some va')). split; [constructor; assumption|].
                 rewrite Nat.sub_diag. simpl.
                 rewrite nth_error_app2 by lia.
                 replace (i + length venv_pre' - length venv_pre') with i by lia.
                 rewrite H2. reflexivity.
              ** rewrite nth_error_app2 in Hnth by lia. rewrite Hlen in Hnth.
                 destruct (x - length venv_pre') as [|k] eqn:Hdiff; [lia|]. simpl in Hnth.
                 simpl. rewrite nth_error_app2 by lia.
                 replace (k + length venv_pre' - length venv_pre') with k by lia.
                 destruct (Forall2_exists2 _ _ _ _ _ H0 Hnth) as [v2 [Hnth' Hvc]].
                 exists (Some (Some v2)). split; [constructor; assumption|]. rewrite Hnth'. reflexivity.
        -- subst. rewrite iter_up_tm.
           destruct (lt_dec x (length venv_pre')).
           ++ simpl. rewrite nth_error_app1 in Hnth by lia.
              apply nth_error_None in Hnth. lia.
           ++ destruct (Nat.eq_dec x (length venv_pre')) as [Heq|Hne].
              ** subst x. rewrite nth_error_app2 in Hnth by lia. rewrite Hlen, Nat.sub_diag in Hnth.
                 simpl in Hnth. discriminate.
              ** rewrite nth_error_app2 in Hnth by lia. rewrite Hlen in Hnth.
                 destruct (x - length venv_pre') as [|k] eqn:Hdiff; [lia|]. simpl in Hnth.
                 apply nth_error_None in Hnth. apply Forall2_length in H0.
                 exists (Some None). split; [constructor|].
                 simpl. rewrite nth_error_app2 by lia.
                 replace (k + length venv_pre' - length venv_pre') with k by lia.
                 assert (nth_error venv' k = None) as -> by (apply nth_error_None; lia).
                 reflexivity.
    + (* tabs *)
      subst. eexists; split; [constructor; eapply vsc_abs; exact Hesc | reflexivity].
    + (* tapp f a *)
      destruct (eval fuel env1 f) as [[vf|]|] eqn:Hf.
      * (* f -> Some (Some vf) *)
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf)
          as [[[vf'|]|] [Hrcf Hf2]]; [| inversion Hrcf | inversion Hrcf].
        inversion Hrcf as [| | ? ? Hvcf]; subst.
        destruct vf as [| | | | | |envf bodyf| ]; try (inversion Hvcf; subst; rewrite Hf2; simpl; eexists; split; [constructor | reflexivity]).
        -- (* vf = vabs envf bodyf *)
           inversion Hvcf as [| | | | | | envf0 envf0' bodyf0 sigma_f Hesc_f | ]; subst.
           rewrite Hf2. simpl.
           destruct (eval fuel env1 a) as [[va|]|] eqn:Ha.
           ++ (* a -> Some (Some va) *)
              destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
                as [[[va'|]|] [Hrca Ha2]]; [| inversion Hrca | inversion Hrca].
              inversion Hrca as [| | ? ? Hvca]; subst.
              rewrite Ha2. simpl.
              (* Need to apply IH on body with extended env_subst_compat *)
              inversion Hesc_f; subst.
              ** (* esc_id *)
                 assert (Hesc_body : env_subst_compat (va :: envf) (va' :: envf0') tvar)
                   by (apply esc_id; constructor; auto).
                 destruct (IHfuel bodyf (va :: envf) (va' :: envf0') tvar _ Hesc_body eq_refl)
                   as [rb [Hrcb Hb2]].
                 eexists. split; [exact Hrcb|].
                 rewrite subst_tm_id in Hb2.
                 rewrite subst_tm_up_tm_tm_tvar. exact Hb2.
              ** (* esc_subst *)
                 assert (Hesc' : env_subst_compat ((va :: venv_pre) ++ va0 :: venv) ((va' :: venv_pre') ++ venv') (upn_tm (length (va' :: venv_pre')) (tvar i .: tvar))).
                 { eapply esc_subst; try eassumption. constructor; assumption. }
                 simpl in Hesc'.
                 destruct (IHfuel bodyf ((va :: venv_pre) ++ va0 :: venv) ((va' :: venv_pre') ++ venv')
                            (upn_tm (S (length venv_pre')) (tvar i .: tvar)) _ Hesc' eq_refl)
                   as [rb [Hrcb Hb2]].
                 eexists. split; [exact Hrcb|].
                 exact Hb2.
           ++ (* a -> Some None *)
              destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
                as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | | inversion Hrca].
              subst. rewrite Ha2. eexists; split; [constructor | reflexivity].
           ++ (* a -> None *)
              destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
                as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | inversion Hrca |].
              subst. rewrite Ha2. eexists; split; [constructor | reflexivity].
      * (* f -> Some None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | | inversion Hrcf].
        rewrite Hf2. simpl. eexists; split; [constructor | reflexivity].
      * (* f -> None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | inversion Hrcf |].
        rewrite Hf2. eexists; split; [constructor | reflexivity].
    + (* ttabs *)
      subst.
      replace (subst_tm (up_ty_ty TVar) (up_ty_tm sigma) body) with (subst_tm TVar sigma body).
      * eexists; split; [constructor; eapply vsc_tabs; exact Hesc | reflexivity].
      * symmetry. apply subst_tm_ext. apply up_ty_ty_id.
        intro n. inversion Hesc; subst.
        -- reflexivity.
        -- apply up_ty_tm_upn_tm_scons_tvar.
    + (* ttapp f A *)
      destruct (eval fuel env1 f) as [[vf|]|] eqn:Hf.
      * (* f -> Some (Some vf) *)
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf)
          as [[[vf'|]|] [Hrcf Hf2]]; [| inversion Hrcf | inversion Hrcf].
        inversion Hrcf as [| | ? ? Hvcf]; subst.
        destruct vf as [| | | | | | |envf bodyf]; try (inversion Hvcf; subst; rewrite Hf2; simpl; eexists; split; [constructor | reflexivity]).
        (* vf = vtabs envf bodyf *)
        inversion Hvcf as [| | | | | | | envf0 envf0' bodyf0 sigma_f Hesc_f]; subst.
        rewrite Hf2. simpl.
        inversion Hesc_f; subst.
        -- (* esc_id *)
           assert (Hesc_body : env_subst_compat envf envf0' tvar) by (apply esc_id; auto).
           destruct (IHfuel bodyf envf envf0' tvar _ Hesc_body eq_refl)
             as [rb [Hrcb Hb2]].
           eexists. split; [exact Hrcb|]. rewrite subst_tm_id in Hb2. rewrite subst_tm_id. exact Hb2.
        -- (* esc_subst *)
           destruct (IHfuel bodyf (venv_pre ++ va :: venv) (venv_pre' ++ venv')
                      (upn_tm (length venv_pre') (tvar i .: tvar)) _ Hesc_f eq_refl)
             as [rb [Hrcb Hb2]].
           eexists. split; [exact Hrcb|]. exact Hb2.
      * (* f -> Some None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | | inversion Hrcf].
        rewrite Hf2. simpl. eexists; split; [constructor | reflexivity].
      * (* f -> None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf)
          as [[[?|]|] [Hrcf Hf2]]; [inversion Hrcf | inversion Hrcf |].
        rewrite Hf2. eexists; split; [constructor | reflexivity].
    + (* tlet A e body *)
      destruct (eval fuel env1 e) as [[ve|]|] eqn:He.
      * (* e -> Some (Some ve) *)
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[ve'|]|] [Hrce He2]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He2. simpl.
        inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
        -- (* esc_id *)
           assert (Hesc_body : env_subst_compat (ve :: env1) (ve' :: env2) tvar)
             by (apply esc_id; constructor; auto).
           destruct (IHfuel body (ve :: env1) (ve' :: env2) tvar _ Hesc_body eq_refl)
             as [rb [Hrcb Hb2]].
           eexists. split; [exact Hrcb|].
           rewrite subst_tm_id in Hb2. rewrite subst_tm_up_tm_tm_tvar. exact Hb2.
        -- (* esc_subst *)
           assert (Hesc' : env_subst_compat ((ve :: venv_pre) ++ va0 :: venv0) ((ve' :: venv_pre') ++ venv0') (upn_tm (length (ve' :: venv_pre')) (tvar i0 .: tvar))).
           { eapply esc_subst; try eassumption. constructor; assumption. }
           simpl in Hesc'.
           destruct (IHfuel body ((ve :: venv_pre) ++ va0 :: venv0) ((ve' :: venv_pre') ++ venv0')
                      (upn_tm (S (length venv_pre')) (tvar i0 .: tvar)) _ Hesc' eq_refl)
             as [rb [Hrcb Hb2]].
           eexists. split; [exact Hrcb|].
           exact Hb2.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | | inversion Hrce].
        rewrite He2. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | inversion Hrce |].
        rewrite He2. eexists; split; [constructor | reflexivity].
    + (* tpair e1 e2 *)
      destruct (eval fuel env1 e1) as [[v1_0|]|] eqn:He1.
      * (* e1 -> Some (Some v1_0) *)
        destruct (IHfuel e1 env1 env2 sigma _ Hesc He1)
          as [[[v1'|]|] [Hrc1 He1']]; [| inversion Hrc1 | inversion Hrc1].
        inversion Hrc1 as [| | ? ? Hvc1]; subst.
        destruct (eval fuel env1 e2) as [[v2_0|]|] eqn:He2.
        -- (* e2 -> Some (Some v2_0) *)
           destruct (IHfuel e2 env1 env2 sigma _ Hesc He2)
             as [[[v2'|]|] [Hrc2 He2']]; [| inversion Hrc2 | inversion Hrc2].
           inversion Hrc2 as [| | ? ? Hvc2]; subst.
           rewrite He1', He2'.
           eexists; split; [constructor; eapply vsc_pair; eassumption | reflexivity].
        -- (* e2 -> Some None *)
           destruct (IHfuel e2 env1 env2 sigma _ Hesc He2)
             as [[[?|]|] [Hrc2 He2']]; [inversion Hrc2 | | inversion Hrc2].
           subst. rewrite He1', He2'. eexists; split; [constructor | reflexivity].
        -- (* e2 -> None *)
           destruct (IHfuel e2 env1 env2 sigma _ Hesc He2)
             as [[[?|]|] [Hrc2 He2']]; [inversion Hrc2 | inversion Hrc2 |].
           subst. rewrite He1', He2'. eexists; split; [constructor | reflexivity].
      * (* e1 -> Some None *)
        subst.
        destruct (IHfuel e1 env1 env2 sigma _ Hesc He1)
          as [[[?|]|] [Hrc1 He1']]; [inversion Hrc1 | | inversion Hrc1].
        rewrite He1'. eexists; split; [constructor | reflexivity].
      * (* e1 -> None *)
        subst.
        destruct (IHfuel e1 env1 env2 sigma _ Hesc He1)
          as [[[?|]|] [Hrc1 He1']]; [inversion Hrc1 | inversion Hrc1 |].
        rewrite He1'. eexists; split; [constructor | reflexivity].
    + (* tmatch_pair e body *)
      destruct (eval fuel env1 e) as [[ve|]|] eqn:He.
      * (* e -> Some (Some ve) *)
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[ve'|]|] [Hrce He']]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        destruct ve as [| be | ze | v1_0 v2_0 | ve0 | ve0 | enve bodye | enve bodye];
          try (inversion Hvce; subst; rewrite He'; simpl; eexists; split; [constructor | reflexivity]).
        (* ve = vpair v1_0 v2_0 *)
        inversion Hvce as [| | | ? ? ? ? Hvc_fst Hvc_snd | | | | ]; subst.
        rewrite He'. simpl.
        inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
        -- (* esc_id *)
           assert (Hesc_body : env_subst_compat (v2_0 :: v1_0 :: env1) (v2' :: v1' :: env2) tvar)
             by (apply esc_id; constructor; [exact Hvc_snd | constructor; [exact Hvc_fst | exact Henv]]).
           destruct (IHfuel body (v2_0 :: v1_0 :: env1) (v2' :: v1' :: env2) tvar _ Hesc_body eq_refl)
             as [rb [Hrcb Hb2]].
           eexists. split; [exact Hrcb|].
           rewrite subst_tm_id in Hb2. rewrite subst_tm_up_tm_tm_up_tm_tm_tvar. exact Hb2.
        -- (* esc_subst *)
           assert (Hesc' : env_subst_compat ((v2_0 :: v1_0 :: venv_pre) ++ va0 :: venv0) ((v2' :: v1' :: venv_pre') ++ venv0') (upn_tm (length (v2' :: v1' :: venv_pre')) (tvar i0 .: tvar))).
           { eapply esc_subst; try eassumption.
             constructor; [exact Hvc_snd | constructor; [exact Hvc_fst | exact Hpre]]. }
           simpl in Hesc'.
           destruct (IHfuel body ((v2_0 :: v1_0 :: venv_pre) ++ va0 :: venv0) ((v2' :: v1' :: venv_pre') ++ venv0')
                      (upn_tm (S (S (length venv_pre'))) (tvar i0 .: tvar)) _ Hesc' eq_refl)
             as [rb [Hrcb Hb2]].
           eexists. split; [exact Hrcb|].
           exact Hb2.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | | inversion Hrce].
        rewrite He'. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | inversion Hrce |].
        rewrite He'. eexists; split; [constructor | reflexivity].
    + (* tinl *)
      destruct (eval fuel env1 el) as [[ve|]|] eqn:He.
      * destruct (IHfuel el env1 env2 sigma _ Hesc He)
          as [[[ve'|]|] [Hrce He2]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He2. eexists; split; [constructor; apply vsc_inl; eauto | reflexivity].
      * subst. destruct (IHfuel el env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | | inversion Hrce].
        rewrite He2. eexists; split; [constructor | reflexivity].
      * subst. destruct (IHfuel el env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | inversion Hrce |].
        rewrite He2. eexists; split; [constructor | reflexivity].
    + (* tinr *)
      destruct (eval fuel env1 er) as [[ve|]|] eqn:He.
      * destruct (IHfuel er env1 env2 sigma _ Hesc He)
          as [[[ve'|]|] [Hrce He2]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He2. eexists; split; [constructor; apply vsc_inr; eauto | reflexivity].
      * subst. destruct (IHfuel er env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | | inversion Hrce].
        rewrite He2. eexists; split; [constructor | reflexivity].
      * subst. destruct (IHfuel er env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He2]]; [inversion Hrce | inversion Hrce |].
        rewrite He2. eexists; split; [constructor | reflexivity].
    + (* tmatch_sum e bl br *)
      destruct (eval fuel env1 e) as [[ve|]|] eqn:He.
      * (* e -> Some (Some ve) *)
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[ve'|]|] [Hrce He']]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        destruct ve as [| be | ze | v1_0 v2_0 | ve0 | ve0 | enve bodye | enve bodye];
          try (inversion Hvce; subst; rewrite He'; simpl; eexists; split; [constructor | reflexivity]).
        -- (* ve = vinl ve0 *)
           inversion Hvce as [| | | | ? ? Hvc_inl | | | ]; subst.
           rewrite He'. simpl.
           inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
           ++ (* esc_id *)
              assert (Hesc_body : env_subst_compat (ve0 :: env1) (v2 :: env2) tvar)
                by (apply esc_id; constructor; [exact Hvc_inl | exact Henv]).
              destruct (IHfuel bl (ve0 :: env1) (v2 :: env2) tvar _ Hesc_body eq_refl)
                as [rb [Hrcb Hb2]].
              eexists. split; [exact Hrcb|].
              rewrite subst_tm_id in Hb2. rewrite subst_tm_up_tm_tm_tvar. exact Hb2.
           ++ (* esc_subst *)
              assert (Hesc' : env_subst_compat ((ve0 :: venv_pre) ++ va0 :: venv0) ((v2 :: venv_pre') ++ venv0') (upn_tm (length (v2 :: venv_pre')) (tvar i0 .: tvar))).
              { eapply esc_subst; try eassumption.
                constructor; [exact Hvc_inl | exact Hpre]. }
              simpl in Hesc'.
              destruct (IHfuel bl ((ve0 :: venv_pre) ++ va0 :: venv0) ((v2 :: venv_pre') ++ venv0')
                         (upn_tm (S (length venv_pre')) (tvar i0 .: tvar)) _ Hesc' eq_refl)
                as [rb [Hrcb Hb2]].
              eexists. split; [exact Hrcb|].
              exact Hb2.
        -- (* ve = vinr ve0 *)
           inversion Hvce as [| | | | | ? ? Hvc_inr | | ]; subst.
           rewrite He'. simpl.
           inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
           ++ (* esc_id *)
              assert (Hesc_body : env_subst_compat (ve0 :: env1) (v2 :: env2) tvar)
                by (apply esc_id; constructor; [exact Hvc_inr | exact Henv]).
              destruct (IHfuel br (ve0 :: env1) (v2 :: env2) tvar _ Hesc_body eq_refl)
                as [rb [Hrcb Hb2]].
              eexists. split; [exact Hrcb|].
              rewrite subst_tm_id in Hb2. rewrite subst_tm_up_tm_tm_tvar. exact Hb2.
           ++ (* esc_subst *)
              assert (Hesc' : env_subst_compat ((ve0 :: venv_pre) ++ va0 :: venv0) ((v2 :: venv_pre') ++ venv0') (upn_tm (length (v2 :: venv_pre')) (tvar i0 .: tvar))).
              { eapply esc_subst; try eassumption.
                constructor; [exact Hvc_inr | exact Hpre]. }
              simpl in Hesc'.
              destruct (IHfuel br ((ve0 :: venv_pre) ++ va0 :: venv0) ((v2 :: venv_pre') ++ venv0')
                         (upn_tm (S (length venv_pre')) (tvar i0 .: tvar)) _ Hesc' eq_refl)
                as [rb [Hrcb Hb2]].
              eexists. split; [exact Hrcb|].
              exact Hb2.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | | inversion Hrce].
        rewrite He'. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He)
          as [[[?|]|] [Hrce He']]; [inversion Hrce | inversion Hrce |].
        rewrite He'. eexists; split; [constructor | reflexivity].
    + (* tbin_op op a b *)
      destruct (eval fuel env1 a) as [[va0|]|] eqn:Ha.
      * (* a -> Some (Some va0) *)
        destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
          as [[[va'|]|] [Hrca Ha2]]; [| inversion Hrca | inversion Hrca].
        inversion Hrca as [| | ? ? Hvca]; subst.
        destruct (eval fuel env1 b) as [[vb0|]|] eqn:Hb.
        -- (* b -> Some (Some vb0) *)
           destruct (IHfuel b env1 env2 sigma _ Hesc Hb)
             as [[[vb'|]|] [Hrcb Hb2]]; [| inversion Hrcb | inversion Hrcb].
           inversion Hrcb as [| | ? ? Hvcb]; subst.
           rewrite Ha2, Hb2.
           rewrite <- (eval_bin_op_val_subst_compat b0 _ _ _ _ Hvca Hvcb).
           destruct (eval_bin_op b0 va0 vb0).
           ++ eexists; split; [constructor; apply val_subst_compat_refl | reflexivity].
           ++ eexists; split; [constructor | reflexivity].
        -- (* b -> Some None *)
           destruct (IHfuel b env1 env2 sigma _ Hesc Hb)
             as [[[?|]|] [Hrcb Hb2]]; [inversion Hrcb | | inversion Hrcb].
           subst. rewrite Ha2, Hb2. eexists; split; [constructor | reflexivity].
        -- (* b -> None *)
           destruct (IHfuel b env1 env2 sigma _ Hesc Hb)
             as [[[?|]|] [Hrcb Hb2]]; [inversion Hrcb | inversion Hrcb |].
           subst. rewrite Ha2, Hb2. eexists; split; [constructor | reflexivity].
      * (* a -> Some None *)
        subst.
        destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | | inversion Hrca].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
      * (* a -> None *)
        subst.
        destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | inversion Hrca |].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
    + (* tif c thn els *)
      destruct (eval fuel env1 c) as [[vc|]|] eqn:Hc.
      * (* cond -> Some (Some vc) *)
        destruct (IHfuel c env1 env2 sigma _ Hesc Hc)
          as [[[vc'|]|] [Hrcc Hc2]]; [| inversion Hrcc | inversion Hrcc].
        inversion Hrcc as [| | ? ? Hvcc]; subst.
        destruct vc as [| [] | zc | v1c v2c | vc0 | vc0 | envc bodyc | envc bodyc];
          inversion Hvcc; subst; rewrite Hc2; simpl;
          try (eexists; split; [constructor | reflexivity]).
        -- (* true *) eapply IHfuel; eauto.
        -- (* false *) eapply IHfuel; eauto.
      * (* cond -> Some None *)
        subst.
        destruct (IHfuel c env1 env2 sigma _ Hesc Hc)
          as [[[?|]|] [Hrcc Hc2]]; [inversion Hrcc | | inversion Hrcc].
        rewrite Hc2. eexists; split; [constructor | reflexivity].
      * (* cond -> None *)
        subst.
        destruct (IHfuel c env1 env2 sigma _ Hesc Hc)
          as [[[?|]|] [Hrcc Hc2]]; [inversion Hrcc | inversion Hrcc |].
        rewrite Hc2. eexists; split; [constructor | reflexivity].
    + (* tdiverge *) subst. eexists; split; [constructor | reflexivity].
    + (* tloop *)
      destruct (eval fuel env1 a) as [[va|]|] eqn:Ha.
      * destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
          as [[[va'|]|] [Hrca Ha2]]; [| inversion Hrca | inversion Hrca].
        inversion Hrca as [| | ? ? Hvca]; subst.
        rewrite Ha2.
        eapply run_loop_subst_compat_fwd.
        -- exact Hvca.
        -- intros v v' Hvcv r0 Hr0.
           eapply IHfuel. eapply env_subst_compat_cons; eauto. exact Hr0.
        -- subst. reflexivity.
      * subst. destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | | inversion Hrca].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
      * subst. destruct (IHfuel a env1 env2 sigma _ Hesc Ha)
          as [[[?|]|] [Hrca Ha2]]; [inversion Hrca | inversion Hrca |].
        rewrite Ha2. eexists; split; [constructor | reflexivity].
Qed.

(* Generalized backward: handles all results *)
Lemma eval_term_subst_compat_bwd: forall fuel t env1 env2 sigma r,
  env_subst_compat env1 env2 sigma ->
  eval fuel env2 (subst_tm TVar sigma t) = r ->
  exists r',
    res_subst_compat r' r /\
    eval fuel env1 t = r'.
Proof.
    induction fuel; intros t env1 env2 sigma r Hesc Heval.
    { simpl in Heval. subst. exists None. split; [constructor | reflexivity]. }
    destruct t as [|b|z|x|A body|f a|L U body|f A|A e body|e1 e2|e body|Binl el|Ainr er|e bl br|b0 a b|c thn els| |a body]; simpl in *.
    + (* tunit *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tbool *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tint32 *) subst. eexists; split; [constructor; constructor | reflexivity].
    + (* tvar x *)
      subst r. inversion Hesc; subst.
      * (* esc_id case *)
        simpl.
        destruct (nth_error env2 x) as [v|] eqn:Hnth2.
        -- destruct (Forall2_exists2_r _ _ _ _ _ H Hnth2) as [v1 [Hnth1 Hvc]].
           exists (Some (Some v1)). rewrite Hnth1. split; [constructor; assumption | reflexivity].
        -- apply Forall2_length in H.
           rewrite nth_error_None in Hnth2.
           exists (Some None). split; [constructor|].
           assert (nth_error env1 x = None) as -> by (apply nth_error_None; lia).
           reflexivity.
      * (* esc_subst case *)
        pose proof (Forall2_length H) as Hlen.
        rewrite iter_up_tm. simpl.
        destruct (lt_dec x (length venv_pre')).
        -- simpl. rewrite nth_error_app1 by lia.
           destruct (nth_error venv_pre' x) as [v|] eqn:Hnth'.
           ++ destruct (Forall2_exists2_r _ _ _ _ _ H Hnth') as [v1 [Hnth1 Hvc]].
              exists (Some (Some v1)). split; [constructor; assumption|].
              rewrite nth_error_app1 by lia. rewrite Hnth1. reflexivity.
           ++ apply nth_error_None in Hnth'.
              exists (Some None). split; [constructor|].
              rewrite nth_error_app1 by lia.
              assert (nth_error venv_pre x = None) as -> by (apply nth_error_None; lia).
              reflexivity.
        -- destruct (Nat.eq_dec x (length venv_pre')) as [Heq|Hne].
           ++ subst x. rewrite Nat.sub_diag. simpl.
              rewrite !nth_error_app2 by lia.
              replace (i + length venv_pre' - length venv_pre') with i by lia.
              rewrite H2.
              exists (Some (Some va)). split; [constructor; assumption|].
              rewrite Hlen, Nat.sub_diag. reflexivity.
           ++ destruct (x - length venv_pre') as [|k] eqn:Hdiff; [lia|].
              simpl. rewrite nth_error_app2 by lia.
              replace (k + length venv_pre' - length venv_pre') with k by lia.
              destruct (nth_error venv' k) as [v|] eqn:Hnth'.
              ** destruct (Forall2_exists2_r _ _ _ _ _ H0 Hnth') as [v1 [Hnth1 Hvc]].
                 exists (Some (Some v1)). split; [constructor; assumption|].
                 rewrite nth_error_app2 by lia.
                 replace (x - length venv_pre) with (S k) by lia.
                 simpl. rewrite Hnth1. reflexivity.
              ** apply nth_error_None in Hnth'. apply Forall2_length in H0.
                 exists (Some None). split; [constructor|].
                 rewrite nth_error_app2 by lia.
                 replace (x - length venv_pre) with (S k) by lia.
                 simpl.
                 assert (nth_error venv k = None) as -> by (apply nth_error_None; lia).
                 reflexivity.
    + (* tabs *)
      subst. eexists; split; [constructor; eapply vsc_abs; exact Hesc | reflexivity].
    + (* tapp f a *)
      destruct (eval fuel env2 (subst_tm TVar sigma f)) as [[vf'|]|] eqn:Hf2.
      * (* f -> Some (Some vf') *)
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf2)
          as [[[vf|]|] [Hrcf Hf1]]; [| inversion Hrcf | inversion Hrcf].
        inversion Hrcf as [| | ? ? Hvcf]; subst.
        destruct vf' as [| | | | | |envf' bodyf'| ]; try (inversion Hvcf; subst; rewrite Hf1; simpl; eexists; split; [constructor | reflexivity]).
        (* vf' = vabs envf' bodyf' — need vf to also be vabs *)
        destruct vf as [| | | | | |envf bodyf| ]; try solve [inversion Hvcf].
        inversion Hvcf as [| | | | | | ? ? ? sigma_f Hesc_f Heq1 Heq2 | ]; subst.
        rewrite Hf1. simpl.
        destruct (eval fuel env2 (subst_tm TVar sigma a)) as [[va'|]|] eqn:Ha2.
        -- (* a -> Some (Some va') *)
           destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
             as [[[va|]|] [Hrca Ha1]]; [| inversion Hrca | inversion Hrca].
           inversion Hrca as [| | ? ? Hvca]; subst.
           rewrite Ha1. simpl.
           inversion Hesc_f as [? ? Henv_f | venv_pre0 venv_pre0' venv0 venv0' i0 va0 va0' Hcl_pre Hcl_venv Hcl_nth1 Hcl_nth2 Hcl_va]; subst.
           ++ (* esc_id *)
              assert (Hesc_body : env_subst_compat (va :: envf) (va' :: envf') tvar)
                by (apply esc_id; constructor; auto).
              replace (subst_tm TVar (up_tm_tm tvar) bodyf) with (subst_tm TVar tvar bodyf)
                by (symmetry; apply subst_tm_ext; [reflexivity | apply up_tm_tm_id]).
              destruct (IHfuel bodyf (va :: envf) (va' :: envf') tvar _ Hesc_body eq_refl)
                as [rb [Hrcb Hb1]].
              eexists. split; [exact Hrcb|]. auto.
           ++ (* esc_subst *)
              assert (Hesc' : env_subst_compat ((va :: venv_pre0) ++ va0 :: venv0) ((va' :: venv_pre0') ++ venv0') (upn_tm (S (length venv_pre0')) (tvar i0 .: tvar))).
              { replace (S (length venv_pre0')) with (length (va' :: venv_pre0')) by (simpl; lia).
                eapply esc_subst; try eassumption. constructor; assumption. }
              destruct (IHfuel bodyf (va :: venv_pre0 ++ va0 :: venv0) (va' :: venv_pre0' ++ venv0')
                         (upn_tm (S (length venv_pre0')) (tvar i0 .: tvar)) _ Hesc' eq_refl)
                as [rb [Hrcb Hb1]].
              eexists. split; [exact Hrcb|]. auto.
        -- (* a -> Some None *)
           destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
             as [[[?|]|] [Hrca Ha1]]; [inversion Hrca | | inversion Hrca].
           subst. rewrite Ha1. eexists; split; [constructor | reflexivity].
        -- (* a -> None *)
           destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
             as [[[?|]|] [Hrca Ha1]]; [inversion Hrca | inversion Hrca |].
           subst. rewrite Ha1. eexists; split; [constructor | reflexivity].
      * (* f -> Some None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf2)
          as [[[?|]|] [Hrcf Hf1]]; [inversion Hrcf | | inversion Hrcf].
        rewrite Hf1. simpl. eexists; split; [constructor | reflexivity].
      * (* f -> None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf2)
          as [[[?|]|] [Hrcf Hf1]]; [inversion Hrcf | inversion Hrcf |].
        rewrite Hf1. eexists; split; [constructor | reflexivity].
    + (* ttabs *)
      subst.
      replace (subst_tm (up_ty_ty TVar) (up_ty_tm sigma) body) with (subst_tm TVar sigma body).
      * eexists; split; [constructor; eapply vsc_tabs; exact Hesc | reflexivity].
      * symmetry. apply subst_tm_ext. apply up_ty_ty_id.
        intro n. inversion Hesc; subst.
        -- reflexivity.
        -- apply up_ty_tm_upn_tm_scons_tvar.
    + (* ttapp f A *)
      destruct (eval fuel env2 (subst_tm TVar sigma f)) as [[vf'|]|] eqn:Hf2.
      * (* f -> Some (Some vf') *)
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf2)
          as [[[vf|]|] [Hrcf Hf1]]; [| inversion Hrcf | inversion Hrcf].
        inversion Hrcf as [| | ? ? Hvcf]; subst.
        destruct vf' as [| | | | | | |envf' bodyf']; try (inversion Hvcf; subst; rewrite Hf1; simpl; eexists; split; [constructor | reflexivity]).
        (* vf' = vtabs *)
        destruct vf as [| | | | | | |envf bodyf]; try solve [inversion Hvcf].
        inversion Hvcf as [| | | | | | | ? ? ? sigma_f Hesc_f]; subst.
        rewrite Hf1. simpl.
        inversion Hesc_f as [? ? Henv_f | venv_pre0 venv_pre0' venv0 venv0' i0 va0 va0' Hcl_pre Hcl_venv Hcl_nth1 Hcl_nth2 Hcl_va]; subst.
        -- (* esc_id *)
           assert (Hesc_body : env_subst_compat envf envf' tvar) by (apply esc_id; auto).
           destruct (IHfuel bodyf envf envf' tvar _ Hesc_body eq_refl)
             as [rb [Hrcb Hb1]].
           eexists. split; [exact Hrcb|]. auto.
        -- (* esc_subst *)
           destruct (IHfuel bodyf (venv_pre0 ++ va0 :: venv0) (venv_pre0' ++ venv0')
                      (upn_tm (length venv_pre0') (tvar i0 .: tvar)) _ Hesc_f eq_refl)
             as [rb [Hrcb Hb1]].
           eexists. split; [exact Hrcb|]. auto.
      * (* f -> Some None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf2)
          as [[[?|]|] [Hrcf Hf1]]; [inversion Hrcf | | inversion Hrcf].
        rewrite Hf1. simpl. eexists; split; [constructor | reflexivity].
      * (* f -> None *)
        subst.
        destruct (IHfuel f env1 env2 sigma _ Hesc Hf2)
          as [[[?|]|] [Hrcf Hf1]]; [inversion Hrcf | inversion Hrcf |].
        rewrite Hf1. eexists; split; [constructor | reflexivity].
    + (* tlet A e body *)
      destruct (eval fuel env2 (subst_tm TVar sigma e)) as [[ve'|]|] eqn:He2.
      * (* e -> Some (Some ve') *)
        destruct (IHfuel e env1 env2 sigma _ Hesc He2)
          as [[[ve|]|] [Hrce He1]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He1. simpl.
        inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
        -- (* esc_id *)
           replace (subst_tm (up_tm_ty TVar) (up_tm_tm tvar) body) with (subst_tm TVar tvar body)
             by (symmetry; apply subst_tm_ext; [apply up_tm_ty_id | apply up_tm_tm_id]).
           assert (Hesc_body : env_subst_compat (ve :: env1) (ve' :: env2) tvar)
             by (apply esc_id; constructor; auto).
           destruct (IHfuel body (ve :: env1) (ve' :: env2) tvar _ Hesc_body eq_refl)
             as [rb [Hrcb Hb1]].
           eexists. split; [exact Hrcb|]. auto.
        -- (* esc_subst *)
           assert (Hesc' : env_subst_compat ((ve :: venv_pre) ++ va0 :: venv0) ((ve' :: venv_pre') ++ venv0') (upn_tm (S (length venv_pre')) (tvar i0 .: tvar))).
           { replace (S (length venv_pre')) with (length (ve' :: venv_pre')) by (simpl; lia).
             eapply esc_subst; try eassumption. constructor; assumption. }
           destruct (IHfuel body (ve :: venv_pre ++ va0 :: venv0) (ve' :: venv_pre' ++ venv0')
                      (upn_tm (S (length venv_pre')) (tvar i0 .: tvar)) _ Hesc' eq_refl)
             as [rb [Hrcb Hb1]].
           eexists. split; [exact Hrcb|]. auto.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He2)
          as [[[?|]|] [Hrce He1]]; [inversion Hrce | | inversion Hrce].
        rewrite He1. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He2)
          as [[[?|]|] [Hrce He1]]; [inversion Hrce | inversion Hrce |].
        rewrite He1. eexists; split; [constructor | reflexivity].
    + (* tpair e1 e2 *)
      destruct (eval fuel env2 (subst_tm TVar sigma e1)) as [[v1'|]|] eqn:He1'.
      * (* e1 -> Some (Some v1') *)
        destruct (IHfuel e1 env1 env2 sigma _ Hesc He1')
          as [[[v1_0|]|] [Hrc1 He1]]; [| inversion Hrc1 | inversion Hrc1].
        inversion Hrc1 as [| | ? ? Hvc1]; subst.
        destruct (eval fuel env2 (subst_tm TVar sigma e2)) as [[v2'|]|] eqn:He2'.
        -- (* e2 -> Some (Some v2') *)
           destruct (IHfuel e2 env1 env2 sigma _ Hesc He2')
             as [[[v2_0|]|] [Hrc2 He2]]; [| inversion Hrc2 | inversion Hrc2].
           inversion Hrc2 as [| | ? ? Hvc2]; subst.
           rewrite He1, He2.
           eexists; split; [constructor; eapply vsc_pair; eassumption | reflexivity].
        -- (* e2 -> Some None *)
           destruct (IHfuel e2 env1 env2 sigma _ Hesc He2')
             as [[[?|]|] [Hrc2 He2]]; [inversion Hrc2 | | inversion Hrc2].
           subst. rewrite He1, He2. eexists; split; [constructor | reflexivity].
        -- (* e2 -> None *)
           destruct (IHfuel e2 env1 env2 sigma _ Hesc He2')
             as [[[?|]|] [Hrc2 He2]]; [inversion Hrc2 | inversion Hrc2 |].
           subst. rewrite He1, He2. eexists; split; [constructor | reflexivity].
      * (* e1 -> Some None *)
        subst.
        destruct (IHfuel e1 env1 env2 sigma _ Hesc He1')
          as [[[?|]|] [Hrc1 He1]]; [inversion Hrc1 | | inversion Hrc1].
        rewrite He1. eexists; split; [constructor | reflexivity].
      * (* e1 -> None *)
        subst.
        destruct (IHfuel e1 env1 env2 sigma _ Hesc He1')
          as [[[?|]|] [Hrc1 He1]]; [inversion Hrc1 | inversion Hrc1 |].
        rewrite He1. eexists; split; [constructor | reflexivity].
    + (* tmatch_pair e body *)
      destruct (eval fuel env2 (subst_tm TVar sigma e)) as [[ve'|]|] eqn:He'.
      * (* e -> Some (Some ve') *)
        destruct (IHfuel e env1 env2 sigma _ Hesc He')
          as [[[ve|]|] [Hrce He]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        destruct ve' as [| be | ze | v1' v2' | ve0' | ve0' | enve' bodye' | enve' bodye'];
          try (inversion Hvce; subst; rewrite He; simpl; eexists; split; [constructor | reflexivity]).
        (* ve' = vpair v1' v2' *)
        destruct ve as [| | | v1_0 v2_0 | | | | ]; try solve [inversion Hvce].
        inversion Hvce as [| | | ? ? ? ? Hvc_fst Hvc_snd | | | | ]; subst.
        rewrite He. simpl.
        inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
        -- (* esc_id *)
           replace (subst_tm (up_tm_ty (up_tm_ty TVar)) (up_tm_tm (up_tm_tm tvar)) body) with (subst_tm TVar tvar body)
             by (symmetry; apply subst_tm_ext; [intro; apply up_tm_ty_id | apply up_tm_tm_up_tm_tm_id]).
           assert (Hesc_body : env_subst_compat (v2_0 :: v1_0 :: env1) (v2' :: v1' :: env2) tvar)
             by (apply esc_id; constructor; [exact Hvc_snd | constructor; [exact Hvc_fst | exact Henv]]).
           destruct (IHfuel body (v2_0 :: v1_0 :: env1) (v2' :: v1' :: env2) tvar _ Hesc_body eq_refl)
             as [rb [Hrcb Hb1]].
           eexists. split; [exact Hrcb|]. auto.
        -- (* esc_subst *)
           assert (Hesc' : env_subst_compat ((v2_0 :: v1_0 :: venv_pre) ++ va0 :: venv0) ((v2' :: v1' :: venv_pre') ++ venv0') (upn_tm (S (S (length venv_pre'))) (tvar i0 .: tvar))).
           { replace (S (S (length venv_pre'))) with (length (v2' :: v1' :: venv_pre')) by (simpl; lia).
             eapply esc_subst; try eassumption.
             constructor; [exact Hvc_snd | constructor; [exact Hvc_fst | exact Hpre]]. }
           destruct (IHfuel body (v2_0 :: v1_0 :: venv_pre ++ va0 :: venv0) (v2' :: v1' :: venv_pre' ++ venv0')
                      (upn_tm (S (S (length venv_pre'))) (tvar i0 .: tvar)) _ Hesc' eq_refl)
             as [rb [Hrcb Hb1]].
           eexists. split; [exact Hrcb|]. auto.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He')
          as [[[?|]|] [Hrce He]]; [inversion Hrce | | inversion Hrce].
        rewrite He. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He')
          as [[[?|]|] [Hrce He]]; [inversion Hrce | inversion Hrce |].
        rewrite He. eexists; split; [constructor | reflexivity].
    + (* tinl *)
      destruct (eval fuel env2 (subst_tm TVar sigma el)) as [[ve'|]|] eqn:He2.
      * destruct (IHfuel el env1 env2 sigma _ Hesc He2)
          as [[[ve|]|] [Hrce He1]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He1. eexists; split; [constructor; apply vsc_inl; eauto | reflexivity].
      * subst. destruct (IHfuel el env1 env2 sigma _ Hesc He2)
          as [[[?|]|] [Hrce He1]]; [inversion Hrce | | inversion Hrce].
        rewrite He1. eexists; split; [constructor | reflexivity].
      * subst. destruct (IHfuel el env1 env2 sigma _ Hesc He2)
          as [[[?|]|] [Hrce He1]]; [inversion Hrce | inversion Hrce |].
        rewrite He1. eexists; split; [constructor | reflexivity].
    + (* tinr *)
      destruct (eval fuel env2 (subst_tm TVar sigma er)) as [[ve'|]|] eqn:He2.
      * destruct (IHfuel er env1 env2 sigma _ Hesc He2)
          as [[[ve|]|] [Hrce He1]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        rewrite He1. eexists; split; [constructor; apply vsc_inr; eauto | reflexivity].
      * subst. destruct (IHfuel er env1 env2 sigma _ Hesc He2)
          as [[[?|]|] [Hrce He1]]; [inversion Hrce | | inversion Hrce].
        rewrite He1. eexists; split; [constructor | reflexivity].
      * subst. destruct (IHfuel er env1 env2 sigma _ Hesc He2)
          as [[[?|]|] [Hrce He1]]; [inversion Hrce | inversion Hrce |].
        rewrite He1. eexists; split; [constructor | reflexivity].
    + (* tmatch_sum e bl br *)
      destruct (eval fuel env2 (subst_tm TVar sigma e)) as [[ve'|]|] eqn:He'.
      * (* e -> Some (Some ve') *)
        destruct (IHfuel e env1 env2 sigma _ Hesc He')
          as [[[ve|]|] [Hrce He]]; [| inversion Hrce | inversion Hrce].
        inversion Hrce as [| | ? ? Hvce]; subst.
        destruct ve' as [| be | ze | v1' v2' | ve0' | ve0' | enve' bodye' | enve' bodye'];
          try (inversion Hvce; subst; rewrite He; simpl; eexists; split; [constructor | reflexivity]).
        -- (* ve' = vinl ve0' *)
           destruct ve as [| | | | ve0 | | | ]; try solve [inversion Hvce].
           inversion Hvce as [| | | | ? ? Hvc_inl | | | ]; subst.
           rewrite He. simpl.
           inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
           ++ (* esc_id *)
              replace (subst_tm (up_tm_ty TVar) (up_tm_tm tvar) bl) with (subst_tm TVar tvar bl)
                by (symmetry; apply subst_tm_ext; [apply up_tm_ty_id | apply up_tm_tm_id]).
              assert (Hesc_body : env_subst_compat (ve0 :: env1) (ve0' :: env2) tvar)
                by (apply esc_id; constructor; [exact Hvc_inl | exact Henv]).
              destruct (IHfuel bl (ve0 :: env1) (ve0' :: env2) tvar _ Hesc_body eq_refl)
                as [rb [Hrcb Hb1]].
              eexists. split; [exact Hrcb|]. auto.
           ++ (* esc_subst *)
              assert (Hesc' : env_subst_compat ((ve0 :: venv_pre) ++ va0 :: venv0) ((ve0' :: venv_pre') ++ venv0') (upn_tm (S (length venv_pre')) (tvar i0 .: tvar))).
              { replace (S (length venv_pre')) with (length (ve0' :: venv_pre')) by (simpl; lia).
                eapply esc_subst; try eassumption.
                constructor; [exact Hvc_inl | exact Hpre]. }
              destruct (IHfuel bl (ve0 :: venv_pre ++ va0 :: venv0) (ve0' :: venv_pre' ++ venv0')
                         (upn_tm (S (length venv_pre')) (tvar i0 .: tvar)) _ Hesc' eq_refl)
                as [rb [Hrcb Hb1]].
              eexists. split; [exact Hrcb|]. auto.
        -- (* ve' = vinr ve0' *)
           destruct ve as [| | | | | ve0 | | ]; try solve [inversion Hvce].
           inversion Hvce as [| | | | | ? ? Hvc_inr | | ]; subst.
           rewrite He. simpl.
           inversion Hesc as [? ? Henv | venv_pre venv_pre' venv0 venv0' i0 va0 va0' Hpre Hvenv Hnth1 Hnth2 Hva]; subst.
           ++ (* esc_id *)
              replace (subst_tm (up_tm_ty TVar) (up_tm_tm tvar) br) with (subst_tm TVar tvar br)
                by (symmetry; apply subst_tm_ext; [apply up_tm_ty_id | apply up_tm_tm_id]).
              assert (Hesc_body : env_subst_compat (ve0 :: env1) (ve0' :: env2) tvar)
                by (apply esc_id; constructor; [exact Hvc_inr | exact Henv]).
              destruct (IHfuel br (ve0 :: env1) (ve0' :: env2) tvar _ Hesc_body eq_refl)
                as [rb [Hrcb Hb1]].
              eexists. split; [exact Hrcb|]. auto.
           ++ (* esc_subst *)
              assert (Hesc' : env_subst_compat ((ve0 :: venv_pre) ++ va0 :: venv0) ((ve0' :: venv_pre') ++ venv0') (upn_tm (S (length venv_pre')) (tvar i0 .: tvar))).
              { replace (S (length venv_pre')) with (length (ve0' :: venv_pre')) by (simpl; lia).
                eapply esc_subst; try eassumption.
                constructor; [exact Hvc_inr | exact Hpre]. }
              destruct (IHfuel br (ve0 :: venv_pre ++ va0 :: venv0) (ve0' :: venv_pre' ++ venv0')
                         (upn_tm (S (length venv_pre')) (tvar i0 .: tvar)) _ Hesc' eq_refl)
                as [rb [Hrcb Hb1]].
              eexists. split; [exact Hrcb|]. auto.
      * (* e -> Some None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He')
          as [[[?|]|] [Hrce He]]; [inversion Hrce | | inversion Hrce].
        rewrite He. eexists; split; [constructor | reflexivity].
      * (* e -> None *)
        subst.
        destruct (IHfuel e env1 env2 sigma _ Hesc He')
          as [[[?|]|] [Hrce He]]; [inversion Hrce | inversion Hrce |].
        rewrite He. eexists; split; [constructor | reflexivity].
    + (* tbin_op op a b *)
      destruct (eval fuel env2 (subst_tm TVar sigma a)) as [[va'|]|] eqn:Ha2.
      * (* a -> Some (Some va') *)
        destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
          as [[[va0|]|] [Hrca Ha1]]; [| inversion Hrca | inversion Hrca].
        inversion Hrca as [| | ? ? Hvca]; subst.
        destruct (eval fuel env2 (subst_tm TVar sigma b)) as [[vb'|]|] eqn:Hb2.
        -- (* b -> Some (Some vb') *)
           destruct (IHfuel b env1 env2 sigma _ Hesc Hb2)
             as [[[vb0|]|] [Hrcb Hb1]]; [| inversion Hrcb | inversion Hrcb].
           inversion Hrcb as [| | ? ? Hvcb]; subst.
           rewrite Ha1, Hb1.
           rewrite (eval_bin_op_val_subst_compat b0 _ _ _ _ Hvca Hvcb).
           destruct (eval_bin_op b0 va' vb').
           ++ eexists; split; [constructor; apply val_subst_compat_refl | reflexivity].
           ++ eexists; split; [constructor | reflexivity].
        -- (* b -> Some None *)
           destruct (IHfuel b env1 env2 sigma _ Hesc Hb2)
             as [[[?|]|] [Hrcb Hb1]]; [inversion Hrcb | | inversion Hrcb].
           subst. rewrite Ha1, Hb1. eexists; split; [constructor | reflexivity].
        -- (* b -> None *)
           destruct (IHfuel b env1 env2 sigma _ Hesc Hb2)
             as [[[?|]|] [Hrcb Hb1]]; [inversion Hrcb | inversion Hrcb |].
           subst. rewrite Ha1, Hb1. eexists; split; [constructor | reflexivity].
      * (* a -> Some None *)
        subst.
        destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
          as [[[?|]|] [Hrca Ha1]]; [inversion Hrca | | inversion Hrca].
        rewrite Ha1. eexists; split; [constructor | reflexivity].
      * (* a -> None *)
        subst.
        destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
          as [[[?|]|] [Hrca Ha1]]; [inversion Hrca | inversion Hrca |].
        rewrite Ha1. eexists; split; [constructor | reflexivity].
    + (* tif c thn els *)
      destruct (eval fuel env2 (subst_tm TVar sigma c)) as [[vc'|]|] eqn:Hc2.
      * (* cond -> Some (Some vc') *)
        destruct (IHfuel c env1 env2 sigma _ Hesc Hc2)
          as [[[vc|]|] [Hrcc Hc1]]; [| inversion Hrcc | inversion Hrcc].
        inversion Hrcc as [| | ? ? Hvcc]; subst.
        destruct vc' as [| [] | zc | v1c v2c | vc0' | vc0' | envc bodyc | envc bodyc];
          inversion Hvcc; subst; rewrite Hc1; simpl;
          try (eexists; split; [constructor | reflexivity]).
        -- (* true *) eapply IHfuel; eauto.
        -- (* false *) eapply IHfuel; eauto.
      * (* cond -> Some None *)
        subst.
        destruct (IHfuel c env1 env2 sigma _ Hesc Hc2)
          as [[[?|]|] [Hrcc Hc1]]; [inversion Hrcc | | inversion Hrcc].
        rewrite Hc1. eexists; split; [constructor | reflexivity].
      * (* cond -> None *)
        subst.
        destruct (IHfuel c env1 env2 sigma _ Hesc Hc2)
          as [[[?|]|] [Hrcc Hc1]]; [inversion Hrcc | inversion Hrcc |].
        rewrite Hc1. eexists; split; [constructor | reflexivity].
    + (* tdiverge *) subst. eexists; split; [constructor | reflexivity].
    + (* tloop *)
      destruct (eval fuel env2 (subst_tm TVar sigma a)) as [[va'|]|] eqn:Ha2.
      * destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
          as [[[va|]|] [Hrca Ha1]]; [| inversion Hrca | inversion Hrca].
        inversion Hrca as [| | ? ? Hvca]; subst.
        rewrite Ha1.
        eapply run_loop_subst_compat_bwd.
        -- exact Hvca.
        -- intros v v' Hvcv r0 Hr0.
           eapply IHfuel. eapply env_subst_compat_cons; eauto. exact Hr0.
        -- subst. reflexivity.
      * subst. destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
          as [[[?|]|] [Hrca Ha1]]; [inversion Hrca | | inversion Hrca].
        rewrite Ha1. eexists; split; [constructor | reflexivity].
      * subst. destruct (IHfuel a env1 env2 sigma _ Hesc Ha2)
          as [[[?|]|] [Hrca Ha1]]; [inversion Hrca | inversion Hrca |].
        rewrite Ha1. eexists; split; [constructor | reflexivity].
Qed.

(** ** Corollaries: substituting a variable for an environment entry *)

(** Forward: result from big env implies result for substituted env. *)
Lemma eval_subst_env_fwd: forall fuel p venv_prefix va venv i r,
  nth_error venv i = Some va ->
  eval fuel (venv_prefix ++ va :: venv) p = r ->
  exists r', res_subst_compat r r' /\
    eval fuel (venv_prefix ++ venv) (subst_tm TVar (upn_tm (length venv_prefix) (tvar i .: tvar)) p) = r'.
Proof.
  intros.
  assert (Hesc : env_subst_compat (venv_prefix ++ va :: venv) (venv_prefix ++ venv) (upn_tm (length venv_prefix) (tvar i .: tvar))) by eauto using esc_subst, Forall2_refl, val_subst_compat_refl.
  exact (eval_term_subst_compat_fwd fuel p _ _ _ _ Hesc H0).
Qed.

(** Backward: result from substituted env implies result for big env. *)
Lemma eval_subst_env_bwd: forall fuel p venv_prefix va venv i r,
  nth_error venv i = Some va ->
  eval fuel (venv_prefix ++ venv) (subst_tm TVar (upn_tm (length venv_prefix) (tvar i .: tvar)) p) = r ->
  exists r', res_subst_compat r' r /\
    eval fuel (venv_prefix ++ va :: venv) p = r'.
Proof.
  intros.
  assert (Hesc : env_subst_compat (venv_prefix ++ va :: venv) (venv_prefix ++ venv) (upn_tm (length venv_prefix) (tvar i .: tvar))) by eauto using esc_subst, Forall2_refl, val_subst_compat_refl.
  exact (eval_term_subst_compat_bwd fuel p _ _ _ _ Hesc H0).
Qed.
