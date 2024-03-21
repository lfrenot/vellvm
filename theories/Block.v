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

Definition blocks_aux_sem (G0 G G': map_cfg) b :=
  MapsTo_id b G /\ G' = (remove_id b G0) /\ wf_map_cfg G'.

Definition blocks_sem (G G': map_cfg) b := blocks_aux_sem G G G' b.

Definition P G0 G := forall G' b, wf_map_cfg G -> wf_map_cfg G0 ->
  ((b, G') ∈ (List.map (blocks_aux G0) (elements G))) <-> blocks_aux_sem G0 G G' b.

Lemma blocks_aux_correct: forall G0 G, P G0 G.
Proof.
  intros G0 G.
  apply map_induction_min; unfold P.
  - intros E He G' B Hwf Hwf0. split.
    * assert (HE: elements E = []) by now apply elements_Empty. now rewrite HE.
    * intros [HE _]. contradict HE. intro. eapply empty_mapsto_iff.
      eapply MapsTo_m. reflexivity. reflexivity. symmetry. apply Eempty. apply He. apply H.
  - intros G1 G2 Hrec idB B HBe HB G' A Hwf2 Hwf0. rewrite Add_add in HB. 
    assert (HidB: B.(blk_id) = idB). {
      apply Hwf2. eapply MapsTo_m. reflexivity. reflexivity. apply HB. now apply add_1.
    } subst.
    replace (elements G2) with ((B.(blk_id), B)::(elements G1)). 2: {
      symmetry. apply eqlistA_eq. now apply elements_Add_Below.
    } apply Below_In in HBe.
    split. intros [H|H]. 3: case (eq_dec A.(blk_id) B.(blk_id)); unfold eq; intros He [HMA [HRA Hwf']].
    * apply pair_equal_spec in H as []. subst A G'. 
    repeat split; trivial.
      + eapply MapsTo_m. reflexivity. reflexivity. apply HB. now apply add_1.
      + now apply remove_wf_map_cfg.
    * apply Hrec in H as [HMA [HRA Hwf']]; trivial.
      assert (Hne: ~ A.(blk_id)===B.(blk_id)). { 
        intro. apply HBe. exists A. eapply MapsTo_m. 4: apply HMA. now symmetry. reflexivity. reflexivity.
      }
      repeat split;trivial.
      + eapply MapsTo_m. reflexivity. reflexivity. apply HB. apply add_2. now apply neq_sym. trivial.
      + eapply wf_map_cfg_add. apply HBe. eapply wf_map_cfg_eq. apply HB. trivial.
    * assert (Heq: A=B). { 
      eapply wf_map_cfg_blk. apply Hwf2. apply HMA. eapply MapsTo_m.  apply He. reflexivity. apply HB. now apply add_1.
    } subst. now left.
    * right. apply Hrec; trivial. eapply wf_map_cfg_add. apply HBe. eapply wf_map_cfg_eq. apply HB. trivial.
      repeat split; trivial.
      eapply add_3. apply neq_sym. apply He. eapply MapsTo_m. reflexivity. reflexivity. symmetry. apply HB. trivial.
Qed.

Lemma blocks_correct: forall G G' b, wf_map_cfg G -> ((b, G') ∈ (blocks G) <-> blocks_sem G G' b).
Proof.
  intros. now apply blocks_aux_correct.
Qed.