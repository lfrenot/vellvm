(** This file defines the [BlockFusion] pattern and its semantic, and proves it is correct. *)

From Vellvm Require Import Syntax ScopeTheory Tactics.
(* From ITree Require Import ITree Eq. *)
From Pattern Require Import Base Patterns.
(* Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
Import gmap Block Head.
(* Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Patterns. *)

(*  Look at the terminator directly.
    We would like to be able to use [successors],
    but that would cause equivalence problems when the condition is a poison value.
    *)
Definition is_seq (A: blk) (id: bid) := match A.(blk_term) with
  | TERM_Br_1 id' => if decide (id=id') then true else false
  | _ => false
end.

Definition BlockFusion_f {S}: (bid * blk * (bid * blk * S) → bool) := fun '(_, A, (idB, _, _)) => is_seq A idB.

Definition BlockFusion {S} (P: Pattern S) :=
    (Block (Head P)) when BlockFusion_f.

Record BlockFusion_sem idA A idB B (G G': ocfg): Prop := {
  EQ: G' = (delete idB (delete idA G));
  NEQ: idA <> idB;
  INA: G !! idA = Some A;
  INB: G !! idB = Some B;
  PRED: predecessors idB G = {[idA]};
  SUC: A.(blk_term) = TERM_Br_1 idB
}.

Lemma is_seq_correct:
  forall A id, is_seq A id = true <->
  A.(blk_term) = TERM_Br_1 id.
Proof.
  unfold is_seq. intros A id. split; intro SUC.
  - case_match; try discriminate. now case_match; subst.
  - case_match; try discriminate. case_match; auto. inversion SUC. now subst.
Qed.

Lemma emptyunion: forall (m: gset bid), m = m∪∅.
Proof.
  apply set_ind. intros x y H. apply leibniz_equiv in H. now subst. set_solver.
  intros x X NIN IH. replace ({[x]} ∪ X ∪ ∅) with ({[x]} ∪ (X ∪ ∅)) by set_solver.
  now rewrite <- IH.
Qed. 

Theorem Pattern_BlockFusion_correct {S}: forall idA A idB B G (P: Pattern S) X,
  (idA, A, (idB, B, X)) ∈ (MatchAll (BlockFusion P) G) <->
  exists G1, X ∈ (MatchAll P G1) /\ BlockFusion_sem idA A idB B G G1.
Proof.
  intros *. unfold BlockFusion.
  rewrite Pattern_When_correct, Pattern_Block_correct. unfold BlockFusion_f.
  setoid_rewrite Pattern_Head_correct. 
  setoid_rewrite is_seq_correct.
  split.
  - intros (SUCC & G' & [] & G0 & [] & INX). exists G0.
    assert (idA <> idB) by (intro; simplify_map_eq).
    split; trivial. split; trivial.
    * set_solver.
    * now simplify_map_eq.
    * assert (EQ: G = <[idA:=A]> G') by (subst G'; now rewrite insert_delete). rewrite EQ. rewrite predecessors_insert.
      rewrite PRED0. assert (EQp: predecessors_acc idB idA A = {[idA]}).
      unfold predecessors_acc, is_predecessor. break_match_goal. trivial. break_match_hyp. discriminate.
      unfold successors in n. rewrite SUCC in n. cbn in n. set_solver.
      rewrite EQp. set_solver. subst. now simplify_map_eq.
  - intros (G' & INX & [EQ NEQ INA INB PRED SUC]). split; trivial. exists (delete idA G). split. split; trivial.
    exists G'. split; trivial. split; trivial. now simplify_map_eq.
    pose proof insert_delete G _ _ INA as INDE. rewrite <- INDE in PRED.
    rewrite predecessors_insert in PRED. 
    assert (EQp: predecessors_acc idB idA A = {[idA]}). {
      unfold predecessors_acc, is_predecessor. break_match_goal. trivial. break_match_hyp. discriminate.
      unfold successors in n. rewrite SUC in n. cbn in n. set_solver.
    }
    pose proof emptyunion {[idA]} as Ee. rewrite Ee in PRED.
    rewrite EQp in PRED.
    eapply union_cancel_l_L; cycle 2. apply PRED.
    assert (idA ∉ predecessors idB (delete idA G)). intro.
    pose proof elem_of_predecessors _ _ H as (b & H1 & H2). rewrite lookup_delete in H1. discriminate.
    set_solver. set_solver. now simplify_map_eq.
    Qed. 