(** * Tactics

    Common tactics lemmas used throughout the development.
*)

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Psatz.

Ltac injects :=
  repeat match goal with
  | [ H: _ = _ |- _ ] => injection H; clear H; intros; subst
  end.

Ltac try_prune x :=
  destruct x eqn:?; try discriminate; try lia; injects; eauto;
  let n := numgoals in guard n < 2.

Ltac prune_branches :=
  match goal with
  | H : context [match ?x with _ => _ end] |- _ => try_prune x
  | H : context [if ?c then _ else _] |- _ => try_prune c
  | |- context [match ?x with _ => _ end] => try_prune x
  | |- context [if ?c then _ else _] => try_prune c
  end.
