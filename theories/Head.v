(** This file defines the function for the [Head] [Pattern], the semantic of the pattern,
    and proves the correctness and completeness of that function.
    It also provides a [predecessors] function and lemmas to reason on it. *)

From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Pattern Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.

(** * This section defines the [predecessors] and [heads] functions and their semantic. *)

Definition predecessors_aux (b id: bid) (bk: blk) := is_predecessor b bk.

Definition predecessors (b : bid) (G : map_cfg) : map_cfg :=
    filter (predecessors_aux b) G.

Definition heads_aux (G: map_cfg) id b acc : list (blk*map_cfg) :=
  if is_empty (predecessors id G)
  then (b, remove id G)::acc
  else acc.

Definition heads (G: map_cfg): list (blk*map_cfg) := fold (heads_aux G) G [].

Record heads_aux_sem (G0 G G': map_cfg) b := {
  EQ: G' = (remove_id b G0);
  WF: wf_map_cfg G';
  MT: MapsTo_id b G;
  PRED: Empty (predecessors b.(blk_id) G0)
}.

Definition heads_sem (G G':map_cfg) (b:blk) := heads_aux_sem G G G' b.

(** * This section contains lemmas used for the proof of corectness and completeness of [Head]'s semantics. *)

Lemma heads_aux_sem_eq: forall G0 G G' G1 b, G' ≡ G -> heads_aux_sem G0 G G1 b <-> heads_aux_sem G0 G' G1 b.
Proof.
  intros GO G G' G1 b EQIV. assert (EQIV': G ≡ G') by now symmetry.
  split; intros [EQ WF MT PRED]; repeat split; trivial;
  eapply MapsTo_m; try apply EQIV; try apply EQIV'; try reflexivity; trivial.
Qed.

Lemma heads_aux_split: forall A B id acc G G',
  (A, G) ∈ (heads_aux G' id B acc) -> Empty (predecessors id G') /\ A = B /\ G = remove id G' \/ (A, G) ∈ acc.
Proof.
  unfold heads_aux. intros A B id acc G G'.
  remember (is_empty (predecessors id G')) as b. induction b; [intros [EQ|IN]|intros IN].
  left. apply pair_equal_spec in EQ as [ ]. rewrite is_empty_iff. now subst.
  all: now right.
Qed.

(** The proof of corectness and completeness of [Head]'s semantics. *)

Lemma heads_aux_correct:
  forall G G0 G' b, wf_map_cfg G -> wf_map_cfg G0 ->
  (b, G') ∈ (fold (heads_aux G0) G []) <-> heads_aux_sem G0 G G' b.
Proof.
  intros G G0. apply fold_rec_bis.
  - intros G1 G2 acc EQ REC. intros. setoid_rewrite heads_aux_sem_eq. 2:apply EQ.
    apply REC; [apply (wf_map_cfg_eq G2)|];trivial. now symmetry.
  - intros. split. try contradiction. intros [_ _ MT _].
    now apply empty_mapsto_iff in MT.
  - intros idB B acc G1 MTB NIN REC G2 A WF WF0.
    assert (HidB: B.(blk_id) = idB). { apply WF. now apply add_1. } subst idB.
    split.
    * intros H. apply heads_aux_split in H as [[EM [EQA EQG]]|IN].
      + subst. split; trivial.
        -- now apply remove_wf_map_cfg.
        -- now apply add_1.
      + assert (H: (heads_aux_sem G0 G1 G2 A)). { 
          apply REC; trivial.
          eapply wf_map_cfg_eq. 2: { apply remove_wf_map_cfg. apply WF. }
          symmetry. now apply remove_add_elim.
        } destruct H as [EQ WF2 MTA PRED]. split; trivial.
        case (eq_dec A.(blk_id) B.(blk_id)); unfold eq; [intros EQID|intros NEQID].
        -- contradict NIN. exists A. apply eq_eq in EQID. now rewrite <- EQID.
        -- eapply add_2. now symmetry. trivial.
    * intros [EQ WF2 MTA PRED]. unfold heads_aux.
      (case (eq_dec A.(blk_id) B.(blk_id)); unfold eq; [intros EQID|intros NEQID]).
      + assert (H: A=B). {
            eapply MapsTo_fun. apply MTA. apply eq_eq in EQID. rewrite EQID. now apply add_1.
          } subst. remember (is_empty (predecessors B.(blk_id) G0)) as b. induction b.
        -- now left.
        -- apply is_empty_iff in PRED. rewrite PRED in Heqb. discriminate.
      + assert (H: (A, G2) ∈ acc). {
          apply REC. eapply add_wf_map_cfg. apply NIN. apply WF. trivial.
          repeat split; trivial. eapply add_3. symmetry. apply NEQID. apply MTA.
        } remember (is_empty (predecessors B.(blk_id) G0)) as b. induction b.
        -- now right.
        -- trivial.
Qed.

Lemma heads_correct:
  forall G G' b, wf_map_cfg G ->
  (b, G') ∈ (heads G) <-> heads_sem G G' b.
Proof.
  intros. now apply heads_aux_correct.
Qed.

(** * This section contains lemmas used to manipulate [predecessors] on a remove,
      e.g. for the proofs of [BlockFusion]. *)

Lemma Proper_predecessor_aux:
  forall id, Proper (eq' ==> Logic.eq ==> Logic.eq) (predecessors_aux id).
Proof.
  now intro.
Qed.

#[global] Hint Resolve Proper_predecessor_aux : core.

Lemma add_predecessor: forall (A B: blk) G G', wf_map_cfg G -> MapsTo_id A G ->
  (predecessors B.(blk_id) (remove_id A G)) ≡ G' -> successors A = [B.(blk_id)] ->
  (predecessors B.(blk_id) G) ≡ (add_id A G').
Proof.
  intros A B G G' WF MTA PRED SUC. rewrite Equal_mapsto_iff in PRED.
  setoid_rewrite filter_iff in PRED; auto.
  apply Equal_mapsto_iff. intros idC C. setoid_rewrite filter_iff; auto. split.
  - intros [MTC PREDC]. case (eq_dec A.(blk_id) idC); unfold eq; [intros EQ|intros NEQ].
    * apply eq_eq in EQ. assert (A=C). eapply MapsTo_fun. apply MTA. now rewrite EQ.
      subst. now apply add_1.
    * apply add_2; trivial. apply PRED. split;trivial. now apply remove_2.
  - intro MTC. case (eq_dec A.(blk_id) idC); unfold eq; [intros EQ|intros NEQ].
    * apply eq_eq in EQ. assert (A=C). eapply MapsTo_fun. 2: apply MTC. apply add_1. now subst.
      subst. split; trivial. unfold predecessors_aux. unfold is_predecessor. rewrite SUC.
      cbn. case (raw_id_eq_dec (blk_id B) (blk_id B)); auto.
    * split.
      + eapply remove_3. apply PRED. eapply add_3. 2: apply MTC. trivial.
      + apply PRED. eapply add_3. 2: apply MTC. trivial.
Qed.

Lemma remove_predecessor:
  forall id A G, wf_map_cfg G -> MapsTo_id A G -> (predecessors id G) ≡ (single A) ->
  (predecessors id (remove_id A G)) ≡ empty.
Proof.
  intros id A G WFG MTA PRED. rewrite Equal_mapsto_iff in PRED.
  setoid_rewrite filter_iff in PRED; auto.
  apply Equal_mapsto_iff. intros idC C. setoid_rewrite filter_iff; auto. split.
  - intros [MTC PREDC]. case (eq_dec A.(blk_id) idC); unfold eq; [intros EQ|intros NEQ].
    * apply eq_eq in EQ. assert (A=C). eapply MapsTo_fun. apply MTA. rewrite EQ. eapply remove_3.
      apply MTC. contradict MTC. intros MTC. eapply remove_mapsto_iff. apply MTC. now subst.
    * eapply add_3. apply NEQ. apply PRED. split; trivial. eapply remove_3. apply MTC.
  - intro MTC. contradict MTC. intro MTC. eapply empty_mapsto_iff. apply MTC.
Qed.