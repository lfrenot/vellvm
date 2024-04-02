(** This file defines an FMap that uses block_ids as keys. *)

From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import IdOT.

(** Define the Map and import the functions and lemmas to work with it. *)
Module Map := FMapAVL.Make(IdOT).
Module MapF := FMapFacts.OrdProperties Map.

Import Map MapF MapF.P MapF.P.F.

(** * Notations used throughout the proofs.
    
  Most importantly [map_cfg]. *)

Notation blk := (block dtyp).
Notation bid := block_id.
Notation ocfg := (ocfg dtyp).

Notation map_cfg := (Map.t blk).
Notation empty := (Map.empty blk).

Infix "∈" := List.In (at level 10).

Infix "===" := eq' (at level 10).

Infix "≡" := Map.Equal (at level 10).

Notation add_id b := (add b.(blk_id) b).
Notation remove_id b := (remove b.(blk_id)).
Notation MapsTo_id b := (MapsTo b.(blk_id) b).

Notation single b := (add_id b empty).

(** * wf_map_cfg

  In this section we introduce a well-formedness condition on map_cfgs,
  which is that a block is mapped on its id.*)

Definition wf_map_cfg (g: map_cfg) := forall id b, MapsTo id b g -> b.(blk_id) = id.

Lemma add_wf_map_cfg: forall id b g, ~In id g -> wf_map_cfg (add id b g) -> wf_map_cfg g.
Proof.
  intros idB B G NIN WF idA A MTA.
  apply WF. apply add_2. intro. contradict NIN.
  exists A. eapply MapsTo_m. apply H.
  reflexivity. reflexivity. trivial. trivial.
Qed.

Lemma remove_wf_map_cfg: forall id g, wf_map_cfg g -> wf_map_cfg (remove id g).
Proof.
  intros b g WF id a MT. 
  apply remove_mapsto_iff in MT as [ ]. now apply WF.
Qed.

Lemma wf_map_cfg_eq: forall G G', G ≡ G' -> wf_map_cfg G -> wf_map_cfg G'.
Proof.
  intros G G' EQ WF id b MT.
  apply WF. eapply Equal_mapsto_iff.
  apply EQ. trivial.
Qed.

Lemma wf_map_cfg_part:
  forall G G1 G2, Partition G G1 G2 ->
  wf_map_cfg G -> wf_map_cfg G1 /\ wf_map_cfg G2.
Proof.
  intros G G1 G2 [DIS EQ] WF. split; intros ? ? ?; apply WF; apply EQ; auto.
Qed.

Lemma wf_map_cfg_blk:
  forall G A idA B, wf_map_cfg G -> MapsTo idA A G -> MapsTo A.(blk_id) B G -> A = B.
Proof.
  intros G A idA B WF MTA MTB.
  assert (B.(blk_id)=A.(blk_id)) by now apply WF.
  assert (A.(blk_id)=idA) by now apply WF. subst.
  eapply MapsTo_fun. apply MTA. trivial.
Qed.

(** * This section contains additional manipulations on Maps. *)

Lemma remove_add_elim:
  forall id B (G: map_cfg), ~In id G -> G ≡ (remove id (add id B G)).
Proof.
  intros idB B G NIN. apply Equal_mapsto_iff. intros idA A.
  split; intros MTA; (induction (eq_dec idA idB) as [EQ|NEQ]; [apply eq_eq in EQ; subst|]).
  - contradict NIN. now exists A.
  - eapply remove_2. now symmetry. apply add_2;trivial. now symmetry.
  - contradict MTA. intro MTA. eapply remove_1. reflexivity. exists A. apply MTA.
  - eapply add_3. symmetry. apply NEQ. eapply remove_3. apply MTA.
Qed.

Lemma Eempty: forall (G: map_cfg), Empty G <-> G ≡ empty.
Proof.
  split.
  - intros EM. apply Equal_mapsto_iff. split; intros MT.
    * contradict MT. apply EM.
    * now apply -> empty_mapsto_iff in MT.
  - intros EQ idB B MT. eapply MapsTo_m in MT; [|reflexivity|reflexivity|symmetry; apply EQ].
    now apply -> empty_mapsto_iff in MT.
Qed.

Lemma Aadd: forall (B:blk) id G G', Add id B G G' <-> G' ≡ (add id B G).
Proof.
  intros B id G G'. unfold Add. split.
  - intros FND. apply Equal_mapsto_iff.
    split; intros H';apply find_mapsto_iff in H'; apply find_mapsto_iff; etransitivity; [symmetry;apply FND|trivial|apply FND|trivial].
  - intros EQ id'. rewrite Equal_mapsto_iff in EQ. remember (find id' G') as o. induction o as [a|].
    * symmetry. apply find_mapsto_iff. apply EQ. now apply find_mapsto_iff.
    * symmetry. apply not_find_in_iff. symmetry in Heqo. apply not_find_in_iff in Heqo.
      intros [A Ha]. apply EQ in Ha. contradict Heqo. now exists A. 
Qed.

Lemma eqlistA_eq: forall (l l': list (bid*blk)), eqlistA (O.eqke (elt:=blk)) l l' -> l = l'.
Proof.
  induction l, l'; trivial; intro H; inversion H.
  destruct a,p.
  assert (Heq: l=l') by now apply IHl. inversion H3. cbn in H6, H7.
  apply eq_eq in H6. now subst.
Qed.

Lemma Below_nIn: forall id (G:map_cfg), Below id G -> ~ In id G.
Proof.
  intros id G HB HI. eapply lt_not_eq. apply HB. apply HI. reflexivity.
Qed.

(** Bellow are lemmas that are not used anymore, they may be removed later. *)

(* Lemma add_wf_map_cfg: forall b g, wf_map_cfg g -> wf_map_cfg (add_id b g).
Proof.
  intros b g WF id a MT.
  apply add_mapsto_iff in MT. destruct MT as [[EQ1 EQ2]|[NEQ MT]].
  - apply eq_eq in EQ1. now subst.
  - now apply WF.
Qed. *)

(* Lemma add_remove_elim1:
  forall id B (G: map_cfg), MapsTo id B G -> G ≡ (add id B (remove id G)).
Proof.
  intros idB B G MTB. apply Equal_mapsto_iff.
  intros idA A. split; intro MTA.
  - induction (eq_dec idB idA) as [EQ|NEQ].
    * apply eq_eq in EQ. subst.
      assert (He: B=A). eapply MapsTo_fun.
      apply MTB. apply MTA. subst. now apply add_1.
    * apply add_2; trivial. now apply remove_2.
  - apply add_mapsto_iff in MTA as [[EQ1 EQ2]| [NEQ MTA]].
    * apply eq_eq in EQ1. now subst.
    * eapply remove_3. apply MTA.
Qed. *)

(* Lemma add_remove_elim2:
  forall id B (G G': map_cfg), MapsTo id B G ->
  G' ≡ (remove id G) -> G ≡ (add id B G').
Proof.
  intros id B G G' EQR EQA.
  etransitivity. apply add_remove_elim1. apply EQR.
  apply add_m; auto. reflexivity.
  now symmetry.
Qed. *)

(* Lemma swap_add:
  forall idB idC B C (G : map_cfg), ~ idB === idC ->
  (add idB B (add idC C G)) ≡ (add idC C (add idB B G)).
Proof.
  intros idB idC B C G NEQ.
  apply Equal_mapsto_iff. intros idA A.
  induction (eq_dec idA idB) as [EQB|NEB]. 2: induction (eq_dec idA idC) as [EQC|NEQC].
  - apply eq_eq in EQB. subst.
    split; intro MT.
    * assert (H: B=A). {
        apply add_mapsto_iff in MT as [[EQ1 EQ2]| [NEQ' MTA]]. trivial. contradict NEQ'. apply eq_refl.
      } subst.
      apply add_2. now symmetry.
      apply add_mapsto_iff. left. now split.
    * assert (H: B=A). {
        apply add_3 in MT. apply add_mapsto_iff in MT as [[EQ1 EQ2]| [NEQ' MTA]].
        trivial. contradict NEQ'. reflexivity. now symmetry.
      } subst.
      apply add_1. reflexivity.
  - apply eq_eq in EQC. subst.
    split; intro MT.
    * assert (H: C=A). {
        apply add_3 in MT. apply add_mapsto_iff in MT as [[EQ1 EQ2]| [NEQ' MTA]].
        trivial. contradict NEQ'. reflexivity. trivial.
      } subst.
      apply add_1. reflexivity.
    * assert (H: C=A). {
        apply add_mapsto_iff in MT as [[EQ1 EQ2]| [NEQ' MTA]].
        trivial. contradict NEQ'. reflexivity.
      } subst.
      apply add_2. trivial. apply add_1. reflexivity.
  - split; intro MT.
    * assert (H': MapsTo idA A G).
      eapply add_3. 2:eapply add_3. 3:apply MT. now symmetry. now symmetry. trivial.
      apply add_2. now symmetry. apply add_2. now symmetry. trivial.
    * assert (H': MapsTo idA A G).
      eapply add_3. 2:eapply add_3. 3:apply MT. now symmetry. now symmetry. trivial.
      apply add_2. now symmetry. apply add_2. now symmetry. trivial.
Qed. *)

(* Lemma filter_m: forall f (G G': map_cfg),
  Proper (eq' ==> Logic.eq ==> Logic.eq) f -> G ≡ G' -> filter f G ≡ (filter f G').
Proof.
  intros ? ? ? ? EQ. apply Equal_mapsto_iff. setoid_rewrite filter_iff; trivial. intros idC C.
  split; intros [H1 H2]; split; trivial; eapply MapsTo_m;
  [reflexivity|reflexivity|symmetry;apply EQ|trivial|reflexivity|reflexivity|apply EQ|trivial].
Qed. *)