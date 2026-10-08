(** * Algorithmic Typing

    A computable type checker [typeof] and its safety theorem: if a term is
    algorithmically typed, evaluating it will not get stuck and the
    returned value will be in the interpretation of its computed type.

    Note: this is included only as a test of the mechanization and is not
    presented in the paper. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Psatz.
Require Import RefinementTypes.Syntax.
Require Import RefinementTypes.Subst.
Require Import RefinementTypes.SubstLemmas.
Require Import RefinementTypes.Tactics.
Require Import RefinementTypes.Avoid.
Require Import RefinementTypes.Wf.
Require Import RefinementTypes.Positivity.
Require Import RefinementTypes.SemanticSubtyping.
Require Import RefinementTypes.SemanticTyping.
Require Import RefinementTypes.FirstOrder.

(** ** Algorithmic typing *)

Fixpoint typeof (gamma: Ctx) (t: Term) : option Ty :=
  match t with
  | tunit => Some TUnit
  | tbool _ => Some TBool
  | tint32 _ => Some TInt32
  | tvar i =>
      match nth_error (ctx_tenv gamma) i with
      | Some T => Some (subst_ty TVar (tm_shift (S i)) T)
      | None => None
      end
  | tabs A b =>
      match typeof (ctx_cons_term gamma A) b with
      | Some B => Some (TFun A B)
      | _ => None
      end
  | tapp f a =>
      match a with
      | tvar i =>
        match typeof gamma f with
        | Some (TFun A B) =>
            match typeof gamma a with
            | Some A' => if ty_eq_dec A A' then Some (subst_ty TVar (tvar i .: tvar) B) else None
            | _ => None
            end
        | _ => None
        end
        | _ => None
      end
  | ttabs L U b =>
      match typeof (ctx_cons_type gamma L U) b with
      | Some B => Some (TForall L U B)
      | _ => None
      end
  | ttapp f A =>
      match typeof gamma f with
      | Some (TForall TBot TTop B) => Some (ty_subst B A)
      | _ => None
      end
  | tlet A e b =>
      match typeof gamma e with
      | Some A' =>
          if ty_eq_dec A A' then
            match typeof (ctx_add_fact (ctx_cons_term gamma A) ((S (ctx_len gamma), tvar 0), (ctx_len gamma, e))) b with
            | Some B => Some (subst_ty TVar (tbool true .: tvar) (avoid_var0 B))
            | _ => None
            end
          else None
      | _ => None
      end
  | tpair e1 e2 =>
      match e1 with
      | tvar i =>
          match typeof gamma e1, typeof gamma e2 with
          | Some A, Some B => Some (TSigma A (subst_ty TVar (abstract_term_var i) B))
          | _, _ => None
          end
      | _ => None
      end
  | tmatch_pair e body =>
      match typeof gamma e with
      | Some (TSigma A B) =>
          match typeof (ctx_cons_term (ctx_cons_term gamma A) B) body with
          | Some C => Some (subst_ty TVar (tbool true .: tvar)
                             (avoid_var0 (subst_ty TVar (tbool true .: tvar) (avoid_var0 C))))
          | None => None
          end
      | _ => None
      end
  | tinl B e =>
      match typeof gamma e with
      | Some A => Some (TSum A B)
      | None => None
      end
  | tinr A e =>
      match typeof gamma e with
      | Some B => Some (TSum A B)
      | None => None
      end
  | tmatch_sum e body_l body_r =>
      match typeof gamma e with
      | Some (TSum A B) =>
          match typeof (ctx_add_fact (ctx_cons_term gamma A) ((ctx_len gamma, e), (S (ctx_len gamma), tinl B (tvar 0)))) body_l,
                typeof (ctx_add_fact (ctx_cons_term gamma B) ((ctx_len gamma, e), (S (ctx_len gamma), tinr A (tvar 0)))) body_r with
          | Some C1, Some C2 =>
              Some (TOr (subst_ty TVar (tbool true .: tvar) (avoid_var0 C1))
                        (subst_ty TVar (tbool true .: tvar) (avoid_var0 C2)))
          | _, _ => None
          end
      | _ => None
      end
  | tbin_op op a b =>
      match typeof gamma a, typeof gamma b with
      | Some Ta, Some Tb =>
          match ty_eq_dec Ta Tb with
          | left _ => if bin_op_ty_compat op Ta then Some (bin_op_result_ty op Ta) else None
          | right _ => None
          end
      | _, _ => None
      end
  | tif c t e =>
      match typeof gamma c with
      | Some TBool =>
          match typeof (ctx_add_fact gamma ((ctx_len gamma, c), (ctx_len gamma, tbool true))) t,
                typeof (ctx_add_fact gamma ((ctx_len gamma, c), (ctx_len gamma, tbool false))) e with
          | Some T1, Some T2 => Some (TOr T1 T2)
          | _, _ => None
          end
      | _ => None
      end
  | tdiverge => Some TBot
  | tloop a body =>
      match typeof gamma a with
      | Some A =>
          match typeof (ctx_cons_term gamma A) body with
          | Some (TSum A' B) =>
              if ty_eq_dec A A' then
                if ty_eq_dec (ren_ty id S A) A then
                  if ty_eq_dec (ren_ty id S B) B then
                    Some B
                  else None
                else None
              else None
          | _ => None
          end
      | None => None
      end
  end.

Theorem full_safety: forall t T gamma,
  typeof gamma t = Some T -> sem_typed gamma t T.
Proof.
  induction t; intros T gamma; intros; simpl in *; injects; repeat prune_branches; subst.
  - (* tunit *) eauto using sem_typed_unit.
  - (* tbool *) eauto using sem_typed_bool.
  - (* tint32 *) eauto using sem_typed_int32.
  - (* tvar  *) eauto using sem_typed_var.
  - (* tabs  *) eauto using sem_typed_abs.
  - (* tapp  *) eauto using sem_typed_app_anf.
  - (* ttabs *) eauto using sem_typed_tabs.
  - (* ttapp *) eapply sem_typed_tapp; [eauto | apply sem_subtype_bot | apply sem_subtype_top].
  - (* tlet  *) eauto using sem_typed_let.
  - (* tpair *) eauto using sem_typed_pair_anf.
  - (* tmatch_pair *) eauto using sem_typed_match_pair.
  - (* tinl *) eauto using sem_typed_inl.
  - (* tinr *) eauto using sem_typed_inr.
  - (* tmatch_sum *)
    eapply sem_typed_match_sum; eauto.
  - (* tbin_op *) eauto using sem_typed_bin_op.
  - (* tif   *) destruct (typeof gamma t1) eqn:?,
                         (typeof (ctx_add_fact gamma ((ctx_len gamma, t1), (ctx_len gamma, tbool true))) t2) eqn:?,
                         (typeof (ctx_add_fact gamma ((ctx_len gamma, t1), (ctx_len gamma, tbool false))) t3) eqn:?;
               repeat prune_branches; try discriminate; injects; eauto using sem_typed_if.
  - (* tdiverge *) eauto using sem_typed_diverge.
  - (* tloop *) eapply sem_typed_loop; [exact e0 | exact e1 | eauto | eauto].
Qed.
