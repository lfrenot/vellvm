(** This file defines the function for the [Head] [Pattern], the semantic of the pattern,
    and proves the correctness and completeness of that function.
    It also provides a [predecessors] function and lemmas to reason on it. *)

From Vellvm Require Import Syntax.
From Pattern Require Import Base.
Require Import List.
Import gmap.

Definition is_empty (S: gset bid) := decide (S = ∅).

Definition heads_aux (G: ocfg) id b acc : list (bid*blk*ocfg) :=
  if is_empty (predecessors id G)
  then (id, b, delete id G)::acc
  else acc.

Definition heads (G: ocfg): list (bid*blk*ocfg) := map_fold (heads_aux G) [] G.

Record heads_aux_sem (G0 G G': ocfg) id b := {
  EQ: G' = delete id G0;
  IN: G !! id = Some b;
  PRED: predecessors id G0 = ∅
}.

Definition heads_sem (G G':ocfg) (id:bid) b := heads_aux_sem G G G' id b.

(** * This section contains lemmas used for the proof of corectness and completeness of [Head]'s semantics. *)

(** The proof of corectness and completeness of [Head]'s semantics. *)

Definition heads_aux_P G0 (s:list (bid*blk*ocfg)) G := forall id b G', (id, b, G') ∈ s <-> heads_aux_sem G0 G G' id b.

Lemma heads_aux_correct:
  forall G G0,
  heads_aux_P G0 (map_fold (heads_aux G0) [] G) G.
Proof.
  intros *. apply map_fold_ind; clear G.
  - unfold heads_aux_P. split; intro H; inversion H. set_solver.
  - unfold heads_aux_P. intros id b G r NIN IH id' b' G'. split.
    * unfold heads_aux. case (is_empty (predecessors id G0)); intros EM IN.
      apply elem_of_cons in IN as [EQ|IN]. apply pair_equal_spec in EQ as [H EQ]. apply pair_equal_spec in H as [-> ->].
      2, 3: apply IH in IN as [EQ IN PRED]. all: split; trivial; now simplify_map_eq.
    * unfold heads_aux. intros [EQ IN PRED].
      case (is_empty (predecessors id G0)); intros EM. case (decide (id=id')); intros DEC; apply elem_of_cons; [left | right].
      subst. pose proof lookup_insert_rev _ _ _ _ IN. now subst.
      2: assert (id <> id') by (intro; now subst).
      all: apply IH; split; trivial; now simplify_map_eq.
Qed.

Lemma heads_correct:
  forall G G' id b,
  (id, b, G') ∈ (heads G) <-> heads_sem G G' id b.
Proof.
  intros. now apply heads_aux_correct.
Qed.

(** * This section contains lemmas used to manipulate [predecessors] on a remove,
      e.g. for the proofs of [BlockFusion]. *)

(* Lemma Proper_predecessor_aux:
  forall id, Proper (eq' ==> Logic.eq ==> Logic.eq) (predecessors_aux id).
Proof.
  now intro.
Qed.

#[global] Hint Resolve Proper_predecessor_aux : core.

Lemma add_predecessor: forall (A B: blk) G G',
  wf_map_cfg G -> MapsTo_id A G ->
  successors A = [B.(blk_id)] ->
  (predecessors B.(blk_id) (remove_id A G)) ≡ G' -> 
  (predecessors B.(blk_id) G) ≡ (add_id A G').
Proof.
  intros A B G G' WF MTA SUC PRED. rewrite Equal_mapsto_iff in PRED.
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
Qed. *)