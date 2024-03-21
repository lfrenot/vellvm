From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import IdOT.

(* cfg definition *)

Module Map := FMapAVL.Make(IdOT).
Module MapF := FMapFacts.OrdProperties Map.

Import Map MapF MapF.P MapF.P.F.
(* Print MapF.P. *)


(* Notations *)

Infix "∈" := List.In (at level 10).

Infix "===" := eq' (at level 10).

Infix "≡" := Equal (at level 10).

Notation blk := (block dtyp).
Notation bid := block_id.
Notation ocfg := (ocfg dtyp).

Notation map_cfg := (Map.t blk).
Notation empty := (empty blk).

Notation add_id b := (add b.(blk_id) b).
Notation remove_id b := (remove b.(blk_id)).
Notation MapsTo_id b := (MapsTo b.(blk_id) b).

Notation single b := (add_id b empty).

(* Definitions *)

Definition wf_map_cfg (g: map_cfg) := forall id b, MapsTo id b g -> b.(blk_id) = id.

(* Proofs *)


Lemma add_wf_map_cfg: forall b g, wf_map_cfg g -> wf_map_cfg (add_id b g).
Proof.
  intros b g Hwf id a H.
  apply add_mapsto_iff in H. destruct H as [[H1 H2]|[H1 H2]].
  - apply eq_eq in H1. now subst.
  - now apply Hwf.
Qed.

Lemma wf_map_cfg_add: forall id b g, ~In id g -> wf_map_cfg (add id b g) -> wf_map_cfg g.
Proof.
  intros idB B G HnI Hwfa idA A HA.
  apply Hwfa. apply add_2. intro. contradict HnI.
  exists A. eapply MapsTo_m. apply H.
  reflexivity. reflexivity. trivial. trivial.
Qed.

Lemma remove_wf_map_cfg: forall id g, wf_map_cfg g -> wf_map_cfg (remove id g).
Proof.
  intros b g Hwf id a H. 
  apply remove_mapsto_iff in H as [ ]. now apply Hwf.
Qed.

Lemma wf_map_cfg_eq: forall G G', G ≡ G' -> wf_map_cfg G -> wf_map_cfg G'.
Proof.
  intros G G' He Hwf. intros id b Hm.
  apply Hwf. eapply Equal_mapsto_iff.
  apply He. trivial.
Qed.

Lemma wf_map_cfg_part:
  forall G G1 G2, Partition G G1 G2 ->
  wf_map_cfg G -> wf_map_cfg G1 /\ wf_map_cfg G2.
Proof.
  intros G G1 G2 [Hd Hs] Hwf. split; intros id b Hm; apply Hwf; apply Hs; auto.
Qed.

Lemma wf_map_cfg_blk:
  forall G A idA B, wf_map_cfg G -> MapsTo idA A G -> MapsTo A.(blk_id) B G -> A=B.
Proof.
  intros.
  assert (B.(blk_id)=A.(blk_id)) by now apply H.
  assert (A.(blk_id)=idA) by now apply H. subst.
  eapply MapsTo_fun. apply H0. trivial.
Qed.

Lemma add_remove_elim1:
  forall id B (G: map_cfg), MapsTo id B G -> G ≡ (add id B (remove id G)).
Proof.
  intros id B G H. apply Equal_mapsto_iff.
  intros k e. split; intro H'.
  - induction (eq_dec id k) as [He|He].
    * apply eq_eq in He. subst.
      assert (He: B=e). eapply MapsTo_fun.
      apply H. apply H'. subst. now apply add_1.
    * apply add_2; trivial. now apply remove_2.
  - apply add_mapsto_iff in H' as [[He H']| [Hne H']].
    * apply eq_eq in He. now subst.
    * eapply remove_3. apply H'.
Qed.

Lemma add_remove_elim2:
  forall id B (G G': map_cfg), MapsTo id B G ->
  G' ≡ (remove id G) -> G ≡ (add id B G').
Proof.
  intros id B G G' Hm He.
  etransitivity. apply add_remove_elim1. apply Hm.
  apply add_m; auto. reflexivity.
  now symmetry.
Qed.

Lemma remove_add_elim1:
  forall id B (G: map_cfg), ~In id G -> G ≡ (remove id (add id B G)).
Proof.
  intros idB B G HnI. apply Equal_mapsto_iff. intros idA A.
  split; intros H; case (eq_dec idA idB); intro H'.
  - apply eq_eq in H'. subst. contradict HnI. now exists A.
  - eapply remove_2. now apply neq_sym. apply add_2;trivial. now apply neq_sym.
  - apply eq_eq in H'. subst. contradict H. intro H. eapply remove_1. reflexivity. exists A. apply H.
  - eapply add_3. apply neq_sym. apply H'. eapply remove_3. apply H.
Qed.

Lemma swap_add:
  forall id id' B B' (G : map_cfg), ~ id === id' ->
  (add id B (add id' B' G)) ≡ (add id' B' (add id B G)).
Proof.
  intros id id' B B' G Hn.
  apply Equal_mapsto_iff. intros k e.
  induction (eq_dec k id) as [b|b]. 2: induction (eq_dec k id') as [b'|b'].
  - apply eq_eq in b. subst.
    split; intro H.
    * assert (He: B=e). {
        apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]]. trivial. contradict H1. apply eq_refl.
      } subst.
      apply add_2. now apply neq_sym.
      apply add_mapsto_iff. left. now split.
    * assert (He: B=e). {
        apply add_3 in H. apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
        trivial. contradict H1. reflexivity. now apply neq_sym.
      } subst.
      apply add_1. reflexivity.
  - apply eq_eq in b'. subst.
    split; intro H.
    * assert (He: B'=e). {
        apply add_3 in H. apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
        trivial. contradict H1. reflexivity. trivial.
      } subst.
      apply add_1. reflexivity.
    * assert (He: B'=e). {
        apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
        trivial. contradict H1. reflexivity.
      } subst e.
      apply add_2. trivial. apply add_1. reflexivity.
  - split; intro H.
    * assert (H': MapsTo k e G).
      eapply add_3. apply neq_sym. apply b'.
      eapply add_3. apply neq_sym. apply b. apply H.
      apply add_2. now apply neq_sym. apply add_2. now apply neq_sym. trivial.
    * assert (H': MapsTo k e G).
      eapply add_3. apply neq_sym. apply b.
      eapply add_3. apply neq_sym. apply b'. apply H.
      apply add_2. now apply neq_sym. apply add_2. now apply neq_sym. trivial.
Qed.

Lemma Eempty: forall (G: map_cfg), Empty G <-> G ≡ empty.
Proof.
  split.
  - intro. apply Equal_mapsto_iff. split.
    * intros H'. contradict H'. apply H.
    * intros H'. now apply -> empty_mapsto_iff in H'.
  - intros H id b H'. eapply MapsTo_m in H'; [|reflexivity|reflexivity|symmetry; apply H].
    now apply -> empty_mapsto_iff in H'.
Qed.

Lemma in_mapsto_iff: forall (G:map_cfg) id, In id G <-> (exists B, MapsTo id B G).
Proof.
  unfold In. unfold Raw.In0. now unfold MapsTo.
Qed.

Lemma filter_m: forall f (G G': map_cfg),
  Proper (eq' ==> Logic.eq ==> Logic.eq) f -> G ≡ G' -> filter f G ≡ (filter f G').
Proof.
  intros ? ? ? ? H. apply Equal_mapsto_iff. setoid_rewrite filter_iff; trivial. intros idC C.
  split; intros [H1 H2]; split; trivial; eapply MapsTo_m;
  [reflexivity|reflexivity|symmetry;apply H|trivial|reflexivity|reflexivity|apply H|trivial].
Qed.

Lemma eqlistA_eq: forall (l l': list (bid*blk)), eqlistA (O.eqke (elt:=blk)) l l' -> l = l'.
Proof.
  induction l, l'; trivial; intro H; inversion H.
  destruct a,p.
  assert (Heq: l=l') by now apply IHl. inversion H3. cbn in H6, H7.
  apply eq_eq in H6. now subst.
Qed.

Lemma Add_add: forall (B:blk) id G G', Add id B G G' <-> G' ≡ (add id B G).
Proof.
  intros B id G G'. unfold Add. split.
  - intros H. apply Equal_mapsto_iff.
    split; intros H';apply find_mapsto_iff in H'; apply find_mapsto_iff; etransitivity; [symmetry;apply H|trivial|apply H|trivial].
  - intros H' id'. rewrite Equal_mapsto_iff in H'. remember (find id' G') as o. induction o as [a|].
    * symmetry. apply find_mapsto_iff. apply H'. now apply find_mapsto_iff.
    * symmetry. apply not_find_in_iff. symmetry in Heqo. apply not_find_in_iff in Heqo.
      intros [A Ha]. apply H' in Ha. contradict Heqo. now exists A. 
Qed.

Lemma Below_In: forall id (G:map_cfg), Below id G -> ~ In id G.
Proof.
  intros id G HB HI. eapply lt_not_eq. apply HB. apply HI. reflexivity.
Qed.