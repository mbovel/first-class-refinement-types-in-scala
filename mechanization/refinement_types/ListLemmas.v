(** * List Lemmas

    General-purpose lemmas about [Forall2] and [nth_error]. *)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Psatz.

(** Register the [Forall2] induction schemes, so that inductives nesting
    [Forall2] (such as [val_weaken_compat]) get nested induction principles
    instead of a [register-all] warning. *)
Scheme All for Forall2.

Lemma Forall2_exists2: forall {A B: Type} (R: A -> B -> Prop) (l1: list A) (l2: list B) (n: nat) (x: A),
  Forall2 R l1 l2 ->
  nth_error l1 n = Some x ->
  exists y, nth_error l2 n = Some y /\ R x y.
Proof.
  intros A B R l1 l2 n x HF2.
  generalize dependent n.
  induction HF2; intros n Hnth.
  - destruct n; discriminate.
  - destruct n; simpl in *.
    + inversion Hnth. subst. exists y. auto.
    + apply IHHF2. exact Hnth.
Qed.

Lemma Forall2_exists2_r: forall {A B: Type} (R: A -> B -> Prop) (l1: list A) (l2: list B) (n: nat) (y: B),
  Forall2 R l1 l2 ->
  nth_error l2 n = Some y ->
  exists x, nth_error l1 n = Some x /\ R x y.
Proof.
  intros A B R l1 l2 n y HF2.
  generalize dependent n.
  induction HF2; intros n Hnth.
  - destruct n; discriminate.
  - destruct n; simpl in *.
    + inversion Hnth. subst. exists x. auto.
    + apply IHHF2. exact Hnth.
Qed.

Lemma Forall2_refl: forall {A: Type} (R: A -> A -> Prop) (l: list A),
  (forall x, R x x) ->
  Forall2 R l l.
Proof. induction l; constructor; auto. Qed.

Lemma Forall_Forall2_refl: forall {A: Type} (R: A -> A -> Prop) (l: list A),
  Forall (fun v => R v v) l ->
  Forall2 R l l.
Proof. induction 1; constructor; auto. Qed.
