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

Definition BlockFusion_sem A B G G' :=
  G' ≡ (remove_id B (remove_id A G)) /\ ~(A.(blk_id) === B.(blk_id)) /\
  MapsTo_id A G /\ MapsTo_id B G /\
  (predecessors B.(blk_id) G) ≡ (single A) /\ successors A = [B.(blk_id)].

Theorem Pat_BlockFusion_correct {S}: forall A B G (P: Pat S) X, wf_map_cfg G ->
  (A, (B, X)) ∈ (MatchAll (BlockFusion P) G) <->
  exists G1, X ∈ (MatchAll P G1) /\ BlockFusion_sem A B G G1.
Proof.
  intros A B G P X Hwf. unfold BlockFusion. split.
  - intros H.
    apply Pat_When_correct in H as [H Hseq]. apply is_seq_correct in Hseq.
    apply Pat_Block_correct in H as [G1 [[HmA [HrA Hwf1]] H]]; trivial.
    apply Pat_Head_correct in H as [G2 [[HrB [Hwf2 [HmB Hp]]] H]]; trivial.
    exists G2. split; trivial.
    repeat split; trivial.
    * etransitivity. apply HrB. now apply remove_m.
    * eapply remove_mapsto_iff. eapply MapsTo_m. reflexivity. reflexivity. symmetry.
      apply HrA. apply HmB.
    * eapply remove_3. eapply MapsTo_m. reflexivity. reflexivity. symmetry. apply HrA. trivial.
    * eapply add_predecessor; trivial. etransitivity.
      2: {apply Eempty. apply Hp. }
      apply filter_m; auto. now symmetry.
  - intros [G2 [HX [H2 [HmA [HmB [Hne [Hp Hs]]]]]]]. remember (remove_id A G) as G1.
    apply Pat_When_correct. rewrite is_seq_correct. split; trivial.
    apply Pat_Block_correct; trivial. exists G1. subst.
    repeat split; trivial. now apply remove_wf_map_cfg.
    apply Pat_Head_correct. now apply remove_wf_map_cfg.
    exists G2. repeat split; trivial.
    * eapply wf_map_cfg_eq. symmetry. apply H2. now repeat apply remove_wf_map_cfg.
    * now eapply remove_2.
    * apply Eempty. etransitivity. apply remove_predecessor; trivial. reflexivity.
Qed.