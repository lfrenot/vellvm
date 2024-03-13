From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Patterns Require Import IdModule.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import IdOT.

Infix "∈" := List.In (at level 10).

(* cfg definition *)

Module Map := FMapAVL.Make(IdOT).
Module MapF := FMapFacts.OrdProperties Map.

Import Map MapF MapF.P MapF.P.F.

(* Notations *)

Infix "===" := eq' (at level 10).

Infix "≡" := Equal (at level 10).

Notation blk := (block dtyp).
Notation bid := block_id.
Notation ocfg := (ocfg dtyp).

Notation map_cfg := (Map.t blk).
Notation empty := (empty blk).

(* Definitions *)

Definition wf_map_cfg (g: map_cfg) := forall id b, MapsTo id b g -> b.(blk_id) = id.

(* Proofs *)

Lemma add_wf_map_cfg: forall b g, wf_map_cfg g -> wf_map_cfg (add b.(blk_id) b g).
Proof.
  intros b g Hwf id a H.
  apply add_mapsto_iff in H. destruct H as [[H1 H2]|[H1 H2]].
  - apply eq_eq in H1. now subst a.
  - now apply Hwf.
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

Lemma swap_add:
  forall id id' B B' (G : map_cfg), ~ id === id' ->
  (add id B (add id' B' G)) ≡ (add id' B' (add id B G)).
Proof.
  intros id id' B B' G Hn.
  apply Equal_mapsto_iff. intros k e.
  induction (eq_dec k id) as [b|b]. 2: induction (eq_dec k id') as [b'|b'].
  - apply eq_eq in b. subst k.
    split; intro H. assert (He: B=e).
    apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]]. trivial. contradict H1. apply eq_refl. subst e.
    apply add_2.
      * now apply neq_sym. 
      * apply add_mapsto_iff. left.
        apply add_mapsto_iff in H as [|[H1 H2]]. trivial. contradict H1. reflexivity.
      * assert (He: B=e).
        apply add_3 in H. apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
        trivial. contradict H1. reflexivity.
        now apply neq_sym.
        subst e.
        apply add_1. reflexivity.
  - apply eq_eq in b'. subst.
    split; intro H.
    * assert (He: B'=e).
      apply add_3 in H. apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
      trivial. contradict H1. reflexivity. trivial.
      subst.
      apply add_1. reflexivity.
    * assert (He: B'=e). apply add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
      trivial. contradict H1. reflexivity. subst e.
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