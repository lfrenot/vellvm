(** This file defines the [BlockFusion] pattern and its semantic, and proves it is correct. *)

From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule MapCFG Patterns.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Patterns.

Definition is_seq (A B: blk) := match successors A with
  | [x] => eqb x B.(blk_id)
  | _ => false
end.

Definition BlockFusion {S} (P: Pattern S) :=
    (Block (Head P)) when (fun '(A, (B, _)) => is_seq A B).

Record BlockFusion_sem A B G G': Prop := {
  EQ: G' = (remove_id B (remove_id A G));
  NEQ: ~(A.(blk_id) === B.(blk_id));
  MTA: MapsTo_id A G;
  MTB: MapsTo_id B G;
  PRED: (predecessors B.(blk_id) G) ≡ (single A);
  SUC: successors A = [B.(blk_id)]
}.

Lemma is_seq_correct:
  forall A B, is_seq A B = true <->
  successors A = [B.(blk_id)].
Proof.
  unfold is_seq. intros A B. split; intro SUC.
  induction (successors A) as [|a l REC]. discriminate. induction l.
  apply eqb_eq in SUC. now subst. discriminate.
  rewrite SUC. now apply eqb_eq.
Qed.

Theorem Pattern_BlockFusion_correct {S}: forall A B G (P: Pattern S) X, wf_map_cfg G ->
  (A, (B, X)) ∈ (MatchAll (BlockFusion P) G) <->
  exists G1, X ∈ (MatchAll P G1) /\ BlockFusion_sem A B G G1.
Proof.
  intros A B G P X WFG. unfold BlockFusion. split.
  - intros H.
    apply Pattern_When_correct in H as [H SUC]. apply is_seq_correct in SUC.
    apply Pattern_Block_correct in H as [G1 [[MTA RMA WF1] H]]; trivial.
    apply Pattern_Head_correct in H as [G2 [[RMB WH2 MTB PRED] H]]; trivial.
    exists G2. split; trivial. subst.
    split; trivial.
    * intro He. eapply remove_1. apply He. exists B. apply MTB.
    * eapply remove_3. apply MTB.
    * eapply add_predecessor; trivial. now apply Eempty.
  - intros [G2 [HX [EQ NEQ MTA MTB PRED SUC]]]. remember (remove_id A G) as G1.
    apply Pattern_When_correct. rewrite is_seq_correct. split; trivial.
    apply Pattern_Block_correct; trivial. exists G1.
    split. split; trivial. subst. now apply remove_wf_map_cfg.
    apply Pattern_Head_correct. subst. now apply remove_wf_map_cfg.
    exists G2. subst. split; trivial. split; trivial.
    * now repeat apply remove_wf_map_cfg.
    * now apply remove_2.
    * apply Eempty. apply remove_predecessor; trivial.
Qed.