From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Pattern Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.

(* Head Definitions *)

Definition predecessors_aux (b id: bid) (bk: blk) := is_predecessor b bk.

Definition predecessors (b : bid) (G : map_cfg) : map_cfg :=
    filter (predecessors_aux b) G.

Definition heads_aux (G: map_cfg) id b acc : list (blk*map_cfg) :=
  if is_empty (predecessors id G)
  then (b, remove id G)::acc
  else acc.

Definition heads (G: map_cfg): list (blk*map_cfg) := fold (heads_aux G) G [].

Definition head_sem (G G':map_cfg) (b:blk) :=
  G' ≡ (remove_id b G) /\ wf_map_cfg G' /\
  MapsTo_id b G /\ Empty (predecessors b.(blk_id) G).

(* Lemmas *)

Lemma Proper_predecessor_aux:
  forall id, Proper (eq' ==> Logic.eq ==> Logic.eq) (predecessors_aux id).
Proof.
  now intro.
Qed.

#[global] Hint Resolve Proper_predecessor_aux : core.

Lemma predecessors_in: forall G id id', In id (predecessors id' G) -> In id G.
Proof.
  intros G id id' Hp. apply in_mapsto_iff in Hp as [B Hp]. apply in_mapsto_iff. exists B.
  apply filter_iff in Hp as [H _]; auto.
Qed.

Lemma add_predecessor: forall (A B: blk) G G', wf_map_cfg G -> MapsTo_id A G ->
  (predecessors B.(blk_id) (remove_id A G)) ≡ G' -> successors A = [B.(blk_id)] ->
  (predecessors B.(blk_id) G) ≡ (add_id A G').
Proof.
  intros A B G G' Hwf HA He Hs. rewrite Equal_mapsto_iff in He. setoid_rewrite filter_iff in He; auto.
  apply Equal_mapsto_iff. intros idC C. setoid_rewrite filter_iff; auto. split.
  - intros [HmC Hp]. case (eq_dec A.(blk_id) idC); unfold eq; intro Heq.
    * apply eq_eq in Heq. assert (A=C). eapply MapsTo_fun. apply HA. now rewrite Heq.
      subst. now apply add_1.
    * apply add_2; trivial. apply He. split;trivial. now apply remove_2.
  - intro HC. case (eq_dec A.(blk_id) idC); unfold eq; intro Heq.
    * apply eq_eq in Heq. assert (A=C). eapply MapsTo_fun. 2: apply HC. apply add_1. now subst.
      subst. split; trivial. unfold predecessors_aux. unfold is_predecessor. rewrite Hs.
      cbn. case (raw_id_eq_dec (blk_id B) (blk_id B)); auto.
    * split.
      + eapply remove_3. apply He. eapply add_3. 2: apply HC. trivial.
      + apply He. eapply add_3. 2: apply HC. trivial.
Qed.

Lemma remove_predecessor:
  forall id A G, wf_map_cfg G -> MapsTo_id A G -> (predecessors id G) ≡ (single A) ->
  (predecessors id (remove_id A G)) ≡ empty.
Proof.
  intros id A G Hwf HA Hp. rewrite Equal_mapsto_iff in Hp. setoid_rewrite filter_iff in Hp; auto.
  apply Equal_mapsto_iff. intros idC C. setoid_rewrite filter_iff; auto. split.
  - intros [HmC HpC]. case (eq_dec A.(blk_id) idC); unfold eq; intro Heq.
    * apply eq_eq in Heq. assert (A=C). eapply MapsTo_fun. apply HA. rewrite Heq. eapply remove_3.
      apply HmC. contradict HmC. intro. eapply remove_mapsto_iff. apply H0. now subst.
    * eapply add_3. apply Heq. apply Hp. split; trivial. eapply remove_3. apply HmC.
  - intro HC. contradict HC. intro HC. eapply empty_mapsto_iff. apply HC.
Qed.

Lemma heads_correct:
  forall G G' b, wf_map_cfg G ->
  (b, G') ∈ (heads G) <-> head_sem G G' b.
Proof.
Admitted.