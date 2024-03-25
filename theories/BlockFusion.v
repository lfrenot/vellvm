(* Block Fusion using the Block pattern *)

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

Definition BlockFusion {S} (P: Pat S) :=
    (Block (Head P)) when (fun '(A, (B, _)) => is_seq A B).

Lemma is_seq_correct:
  forall A B, is_seq A B = true <->
  successors A = [B.(blk_id)].
Proof.
  unfold is_seq. intros A B. split; intro H.
  induction (successors A) as [|a l IHl]. discriminate. induction l.
  apply eqb_eq in H. now subst. discriminate.
  rewrite H. now apply eqb_eq.
Qed.

Record BlockFusion_sem A B G G': Prop := {
  EQ: G' = (remove_id B (remove_id A G));
  NEQ: ~(A.(blk_id) === B.(blk_id));
  MTA: MapsTo_id A G;
  MTB: MapsTo_id B G;
  PRED: (predecessors B.(blk_id) G) ≡ (single A);
  SUC: successors A = [B.(blk_id)]
}.

Theorem Pat_BlockFusion_correct {S}: forall A B G (P: Pat S) X, wf_map_cfg G ->
  (A, (B, X)) ∈ (MatchAll (BlockFusion P) G) <->
  exists G1, X ∈ (MatchAll P G1) /\ BlockFusion_sem A B G G1.
Proof.
  intros A B G P X WFG. unfold BlockFusion. split.
  - intros H.
    apply Pat_When_correct in H as [H SUC]. apply is_seq_correct in SUC.
    apply Pat_Block_correct in H as [G1 [[MTA RMA WF1] H]]; trivial.
    apply Pat_Head_correct in H as [G2 [[RMB WH2 MTB PRED] H]]; trivial.
    exists G2. split; trivial. subst.
    repeat split; trivial.
    * intro He. eapply remove_1. apply He. exists B. apply MTB.
    * eapply remove_3. apply MTB.
    * eapply add_predecessor; trivial. now apply Eempty.
  - intros [G2 [HX [EQ NEQ MTA MTB PRED SUC]]]. remember (remove_id A G) as G1.
    apply Pat_When_correct. rewrite is_seq_correct. split; trivial.
    apply Pat_Block_correct; trivial. exists G1.
    repeat split; trivial. subst. now apply remove_wf_map_cfg.
    apply Pat_Head_correct. subst. now apply remove_wf_map_cfg.
    exists G2. subst. repeat split; trivial.
    * now repeat apply remove_wf_map_cfg.
    * now eapply remove_2.
    * apply Eempty. apply remove_predecessor; trivial.
Qed.