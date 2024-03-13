From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Patterns Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.

(* Head Definitions *)

Definition predecessors_aux (b id: bid) (bk: blk) acc :=
  if is_predecessor b bk
  then add id bk acc
  else acc.

Definition predecessors (b : bid) (G : map_cfg) : map_cfg :=
    fold (predecessors_aux b) G empty.

Definition find_heads_aux (G: map_cfg) id b acc : list (blk*map_cfg) :=
  if is_empty (predecessors id G)
  then (b, remove id G)::acc
  else acc.

Definition find_heads (G: map_cfg): list (blk*map_cfg) := fold (find_heads_aux G) G [].

Definition is_head (G G':map_cfg) (b:blk) :=
  G' ≡ (remove b.(blk_id) G) /\ wf_map_cfg G' /\
  MapsTo b.(blk_id) b G /\ Empty (predecessors b.(blk_id) G).

Lemma Proper_predecessor_aux:
  forall id, Proper (eq ==> Logic.eq ==> Equal ==> Equal) (predecessors_aux id).
Proof.
  intros id idB idB' H B B' H0 x1 y1 H1 y2. apply eq_eq in H. subst B' idB'.
  unfold predecessors_aux. remember (is_predecessor id B) as b. induction b.
  - apply find_m. reflexivity. apply add_m; trivial. reflexivity.
  - apply find_m; trivial. reflexivity.
Qed.

Lemma transpose_neqkey_predecessor_aux:
    forall id, transpose_neqkey Equal (predecessors_aux id).
Proof.
  intros id idB idB' B B' G H id'.
  unfold predecessors_aux. remember (is_predecessor id B) as b. remember (is_predecessor id B') as b'.
  induction b, b'; trivial.
  apply find_m. reflexivity. now apply swap_add.
Qed.

#[global] Hint Resolve Proper_predecessor_aux : core.
#[global] Hint Resolve transpose_neqkey_predecessor_aux : core.

Lemma predecessors_in: forall G id id', In id (predecessors id' G) -> In id G.
Proof.
  unfold predecessors. intros G id id'. eapply fold_rec_bis.
  - intros G1 G2 G3 He Him Hi. eapply In_m. reflexivity. symmetry.
    apply He. apply Him. apply Hi.
  - trivial.
  - intros idb B G1 G2 Hm Hni Him Hip.
    unfold predecessors_aux in Hip. remember (is_predecessor id' B) as b. induction b.
    apply add_in_iff in Hip as [Hip|Hip].
    * apply add_in_iff. now left.
    * apply add_in_iff. right. now apply Him.
    * apply add_in_iff. right. now apply Him.
Qed.

Lemma predecessors_aux_empty_acc: forall G id id' acc,
  In id (predecessors id' G) ->
  In id (fold (predecessors_aux id') G acc).
Proof.
  unfold predecessors. intros G id id'. eapply fold_rec_bis.
  intros G1 G2 G3 He H1 acc H3.
  - eapply In_m. reflexivity. 2:apply H1.
    apply fold_Equal; auto. now symmetry. trivial.
  - intros acc H. now apply empty_in_iff in H.
  - intros idB B G1 G2 Hm Hni Him acc Hip.
    unfold predecessors_aux in Hip.
    eapply In_m. reflexivity.
    assert (H:  (fold (predecessors_aux id') (add idB B G2) acc) ≡
                ((predecessors_aux id') idB B (fold (predecessors_aux id') G2 acc))
           ).
    apply fold_add; auto. apply H.
    unfold predecessors_aux at 1. remember (is_predecessor id' B) as b. induction b.
    * apply add_in_iff in Hip as [Hip|Hip]. apply add_in_iff. now left.
      apply add_in_iff. right. now apply Him.
    * now apply Him.
Qed. 

Lemma add_predecessor: forall (A B: blk) G, wf_map_cfg G -> MapsTo (blk_id A) A G ->
  Empty (predecessors B.(blk_id) (remove A.(blk_id) G)) -> successors A = [B.(blk_id)] ->
  (predecessors B.(blk_id) G) ≡ (add A.(blk_id) A empty).
Proof.
  intros. remember (remove (elt:=blk) (blk_id A) G) as G'.
  assert (H': G ≡ (add A.(blk_id) A G')).
  {
    apply add_remove_elim2. trivial. rewrite HeqG'. reflexivity.
  }
  unfold predecessors. erewrite fold_Equal;auto. 2: apply H'.
  etransitivity.
    - assert (H3: (fold (predecessors_aux (blk_id B)) (add (blk_id A) A G') empty) ≡
              (predecessors_aux (blk_id B) (blk_id A) A (fold (predecessors_aux (blk_id B)) G' empty))
             ).
    {
      apply fold_add; auto.
      rewrite HeqG'. apply remove_1. reflexivity.
    }
    apply H3.
  - etransitivity.
    * apply Proper_predecessor_aux. reflexivity. reflexivity. apply Eempty. apply H1.
    * unfold predecessors_aux. unfold is_predecessor. rewrite H2. cbn.
      induction (raw_id_eq_dec (blk_id B) (blk_id B)). reflexivity. contradiction.
Qed.

Lemma is_head_eq:
  forall G G' H H' A,
  G ≡ H -> G' ≡ H' ->
  is_head G G' A -> is_head H H' A.
Proof.
  unfold is_head. intros G G' H H' B He He' [Her [Hwf' [Hm Hp]]]. repeat split.
  - etransitivity. 2:etransitivity.
    * symmetry. apply He'.
    * apply Her.
    * eapply remove_m. reflexivity. trivial.
  - eapply wf_map_cfg_eq. apply He'. trivial.
  - eapply MapsTo_m. reflexivity. reflexivity. symmetry. apply He. trivial.
  - apply Eempty. etransitivity. unfold predecessors. apply fold_Equal; auto.
    symmetry. apply He. now apply Eempty.
Qed.

Lemma head_correct: forall G G' b, wf_map_cfg G -> ((b, G') ∈ (find_heads G) <-> is_head G G' b).
Proof.
Admitted.