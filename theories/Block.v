(** This file defines the function for the [Block] [Pattern], the semantic of the pattern,
    and proves the correctness and completeness of that function. *)

From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Pattern Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.

Definition blocks_aux (G: map_cfg) : _ -> (blk*map_cfg) := fun '(id, b) => (b, remove id G).

Definition blocks (G: map_cfg): list (blk*map_cfg) := List.map (blocks_aux G) (elements G).

Record blocks_aux_sem (G0 G G': map_cfg) b : Prop := 
  {
    MT: MapsTo_id b G;
    RM: G' = remove_id b G0;
    WF: wf_map_cfg G'
  }.

Definition blocks_sem (G G': map_cfg) b := blocks_aux_sem G G G' b.

Definition P G0 G := forall G' b, wf_map_cfg G -> wf_map_cfg G0 ->
  ((b, G') ∈ (List.map (blocks_aux G0) (elements G))) <-> blocks_aux_sem G0 G G' b.

Lemma blocks_aux_correct: forall G0 G, P G0 G.
Proof.
  intros G0 G.
  apply map_induction_min; unfold P.
  - intros E Em G' B WFE WF0. split.
    * assert (Enil: elements E = []) by now apply elements_Empty. now rewrite Enil.
    * intros [MTE _ _]. contradict MTE. intro MTE. eapply empty_mapsto_iff.
      eapply MapsTo_m. reflexivity. reflexivity. symmetry. apply Eempty. apply Em. apply MTE.
  - intros G1 G2 REC idB B Bel EQ2 G' A WF2 WF0. rewrite Aadd in EQ2. apply Below_nIn in Bel as NIN.
    assert (BidB: B.(blk_id) = idB). {
      apply WF2. eapply MapsTo_m. reflexivity. reflexivity. apply EQ2. now apply add_1.
    } subst.
    replace (elements G2) with ((B.(blk_id), B)::(elements G1)). 2: {
      symmetry. apply eqlistA_eq. now apply elements_Add_Below.
    } 
    split. intros [H|H].
    3: case (eq_dec A.(blk_id) B.(blk_id)); unfold eq ; [intros EQ|intros NEQ]; intros [MT2 RM0 WF'].
    * apply pair_equal_spec in H as []. subst A G'. 
      repeat split; trivial.
      + eapply MapsTo_m. reflexivity. reflexivity. apply EQ2. now apply add_1.
      + now apply remove_wf_map_cfg.
    * apply REC in H as [HM1 HR0 WF']; trivial.
      assert (NEQ: ~ A.(blk_id)===B.(blk_id)). { 
        intro. apply NIN. exists A. eapply MapsTo_m. 4: apply HM1. now symmetry. reflexivity. reflexivity.
      }
      repeat split;trivial.
      + eapply MapsTo_m. reflexivity. reflexivity. apply EQ2. apply add_2. now symmetry. trivial.
      + eapply add_wf_map_cfg. apply NIN. eapply wf_map_cfg_eq. apply EQ2. trivial.
    * assert (Heq: A=B). { 
      eapply wf_map_cfg_blk. apply WF2. apply MT2. eapply MapsTo_m.
      apply EQ. reflexivity. apply EQ2. now apply add_1.
    } subst. now left.
    * right. apply REC; trivial. eapply add_wf_map_cfg. apply NIN. eapply wf_map_cfg_eq. apply EQ2. trivial.
      repeat split; trivial.
      eapply add_3. symmetry. apply NEQ. eapply MapsTo_m.
      reflexivity. reflexivity. symmetry. apply EQ2. trivial.
Qed.

Lemma blocks_correct: forall G G' b, wf_map_cfg G -> ((b, G') ∈ (blocks G) <-> blocks_sem G G' b).
Proof.
  intros. now apply blocks_aux_correct.
Qed.