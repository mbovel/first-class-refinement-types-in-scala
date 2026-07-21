(** * Adequacy (Theorems 3.1 and 3.2)

    Syntactic subtyping and typing imply their semantic counterparts. The
    proofs proceed by induction on the derivation, applying the
    corresponding semantic lemma at each constructor. *)

Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.SemanticSubtyping.
Require Import RefinementTypes.SemanticTyping.
Require Import RefinementTypes.SyntacticSubtyping.
Require Import RefinementTypes.SyntacticTyping.

(** Adequacy of subtyping (Theorem 3.2). *)
Theorem syn_subtype_adequate : forall tbounds tenv facts A B,
  syn_subtype tbounds tenv facts A B ->
  sem_subtype tbounds tenv facts A B.
Proof.
  intros * H. induction H.
  - apply sem_subtype_refl.
  - eapply sem_subtype_trans; eassumption.
  - apply sem_subtype_fun; assumption.
  - apply sem_subtype_forall; assumption.
  - apply sem_subtype_sigma; assumption.
  - apply sem_subtype_or_l.
  - apply sem_subtype_or_r.
  - apply sem_subtype_or; assumption.
  - apply sem_subtype_and_l.
  - apply sem_subtype_and_r.
  - apply sem_subtype_and; assumption.
  - apply sem_subtype_refine_base.
  - apply sem_subtype_refine; assumption.
  - apply sem_subtype_top.
  - apply sem_subtype_bot.
  - eapply sem_subtype_tvar_upper; eassumption.
  - eapply sem_subtype_tvar_lower; eassumption.
  - apply sem_subtype_mu_unfold; assumption.
  - apply sem_subtype_mu_fold; assumption.
Qed.

(** Adequacy of typing (Theorem 3.1). *)
Theorem syn_typed_adequate : forall tbounds tenv facts t T,
  syn_typed tbounds tenv facts t T ->
  sem_typed tbounds tenv facts t T.
Proof.
  intros * H. induction H.
  - apply sem_typed_diverge.
  - apply sem_typed_unit.
  - apply sem_typed_bool.
  - apply sem_typed_int32.
  - apply sem_typed_var; assumption.
  - apply sem_typed_abs; assumption.
  - eapply sem_typed_app_anf; eassumption.
  - apply sem_typed_tabs; assumption.
  - eapply sem_typed_tapp; eassumption.
  - eapply sem_typed_let; eassumption.
  - eapply sem_typed_bin_op; eassumption.
  - apply sem_typed_if; assumption.
  - exact (sem_typed_loop _ _ _ _ _ _ _ H H0 IHsyn_typed1 IHsyn_typed2).
  - apply sem_typed_selfify; assumption.
  - eapply sem_typed_sub.
    + exact IHsyn_typed.
    + apply syn_subtype_adequate. exact H0.
  - eapply sem_typed_pair_anf; eassumption.
  - eapply sem_typed_match_pair; eassumption.
  - apply sem_typed_inl; assumption.
  - apply sem_typed_inr; assumption.
  - eapply sem_typed_match_sum; eassumption.
Qed.
