(** This file defines the function for the [Block] [Pattern], the semantic of the pattern,
    and proves the correctness and completeness of that function. *)

From Vellvm Require Import Syntax ScopeTheory Semantics.
(* From ITree Require Import ITree Eq. *)
(* Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
Import gmap.
(* Import ListNotations. *)
From Pattern Require Import Base.
(* Import Map MapF MapF.P MapF.P.F. *)
(* Import IdOT MapCFG. *)

Definition blocks_aux (G: ocfg) : (bid*blk) -> (bid*blk*ocfg) := fun '(id, b) => (id, b, delete id G).

Definition blocks (G: ocfg): list (bid*blk*ocfg) := map (blocks_aux G) (map_to_list G).

Record blocks_aux_sem (G0 G G': ocfg) id b : Prop := 
  {
    EQ: G' = delete id G0;
    IN: G !! id = Some b
  }.

Definition blocks_sem (G G': ocfg) id b := blocks_aux_sem G G G' id b.

Lemma blocks_aux_correct: forall G G0 G' id b, 
  (id, b, G') ∈ map (blocks_aux G0) (map_to_list G) <-> blocks_aux_sem G0 G G' id b.
Proof.
  intros G. apply map_ind with (m:=G).
  - split. set_solver. intros []. inversion IN0.
  - clear G. intros id b G NIN IH G0 G' id' b'. rewrite map_to_list_insert; trivial; cbn. split.
    * intros IN.
      apply elem_of_cons in IN as [EQ|IN];
        [apply pair_equal_spec in EQ as [H EQ]; apply pair_equal_spec in H as [-> ->]|apply IH in IN as []];
        split; trivial; now simplify_map_eq.
    * intros [EQ IN]. case (decide (id=id')); intros DEC; apply elem_of_cons; [left|right].
      + subst. pose proof lookup_insert_rev _ _ _ _ IN. now subst.
      + apply IH. split; trivial; now simplify_map_eq.
Qed.

Lemma blocks_correct: forall G G' id b, (id, b, G') ∈ blocks G <-> blocks_sem G G' id b.
Proof.
  intros. now apply blocks_aux_correct.
Qed.