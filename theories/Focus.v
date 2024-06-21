From Vellvm Require Import Syntax.
Require Import List.
From Pattern Require Import Base.
Import gmap.

Definition focus_aux id b acc : list ocfg := acc ++ ((insert id b) <$> acc).

Definition focus_aux2 (G G1: ocfg) : ocfg*ocfg := (G1, G∖G1).

Definition focus (G: ocfg) := (focus_aux2 G) <$> (map_fold focus_aux [∅] G).

Record focus_sem (G G1 G2: ocfg): Prop := {
  PART: G1 ##ₘ G2;
  CUP: G1 ∪ G2 = G
}.

Lemma map_equiv_empty_L: forall (G:ocfg), G⊆∅ -> G = ∅.
Proof.
  intros G. apply map_ind with (m:=G). auto.
  intros. rewrite map_subseteq_spec in H1. assert (<[i:=x]> m !! i = Some x) by now simplify_map_eq.
  pose proof H1 i x H2. contradict H3. apply lookup_empty_Some.
Qed.

Lemma Proper_focus_aux: forall (j : bid) (z : blk), Proper (equiv ==> equiv) (focus_aux j z).
Proof.
  intros id' b' l1 l2 EQ ?. unfold focus_aux. rewrite !elem_of_app.
  split; intros [H|H].
  - left. now apply EQ.
  - right. apply elem_of_list_fmap in H as (x' & -> & H). apply elem_of_list_fmap. exists x'.
    split; trivial. now apply EQ.
  - left. now apply EQ.
  - right. apply elem_of_list_fmap in H as (x' & -> & H). apply elem_of_list_fmap. exists x'.
    split; trivial. now apply EQ.
Qed.

Lemma com_focus_aux (id: bid) (b: blk) (G: ocfg): forall (j1 j2 : bid) (z1 z2 : blk) (y : list (gmap bid blk)), j1 ≠ j2 → <[id:=b]> G !! j1 = Some z1 → <[id:=b]> G !! j2 = Some z2 → focus_aux j1 z1 (focus_aux j2 z2 y) ≡ focus_aux j2 z2 (focus_aux j1 z1 y).
Proof.
  intros * NEQ IN1 IN2 ?. unfold focus_aux. rewrite <- !app_assoc.
  split; intros H; apply elem_of_app in H as [H|H].
  1,3: apply elem_of_app; now left.
  all: apply elem_of_app in H as [H|H].
  all: apply elem_of_app; right; apply elem_of_app; apply elem_of_list_fmap in H as (x' & -> & H).
  2,4: apply elem_of_app in H as [H|H].
  - right. apply elem_of_list_fmap. exists x'.
    split; trivial. apply elem_of_app. now left.
  - left. apply elem_of_list_fmap. now exists x'.
  - right. apply elem_of_list_fmap in H as (x'' & -> & H).
    apply elem_of_list_fmap. exists (<[j1:=z1]> x''). split. now apply insert_commute.
    apply elem_of_app. right. apply elem_of_list_fmap. now exists x''.
  - left. apply elem_of_list_fmap. now exists x'.
  - right. apply elem_of_list_fmap in H as (x'' & -> & H).
    apply elem_of_list_fmap. exists (<[j2:=z2]> x''). split. now apply insert_commute.
    apply elem_of_app. right. apply elem_of_list_fmap. now exists x''.
  - right. apply elem_of_list_fmap. exists x'.
    split; trivial. apply elem_of_app. now left.
Qed.

Lemma focus_aux_correct: forall G G1, G1 ∈ map_fold focus_aux [∅] G <-> G1 ⊆ G.
Proof. 
  intros G. apply map_fold_ind with (m:=G); clear G.
  - intros. rewrite map_fold_empty, elem_of_list_singleton. split. now intros <-. intros. now apply map_equiv_empty_L.
  - intros id b G L NIN IH G1. split.
    * intros IN. erewrite map_fold_insert in IN; trivial.
      + unfold focus_aux in IN at 1. apply elem_of_app in IN as [IN|IN].
        rewrite IH in IN. apply insert_subseteq_r. eapply lookup_weaken_None. apply NIN. trivial. trivial.
        apply elem_of_list_fmap in IN as (G' & -> & IN).
        apply insert_mono. now apply IH.
      + apply Equivalence_PreOrder. apply set_equiv_equivalence.
      + apply Proper_focus_aux.
      + apply com_focus_aux.
    * intros H. erewrite map_fold_insert; trivial.
      + unfold focus_aux at 1. apply elem_of_app. {
          case (decide (is_Some (G1!!id))) as [IN|NIN'].
          - destruct IN as [x IN]. assert (x=b) as ->. eapply lookup_weaken_inv. apply IN. apply H. now simplify_map_eq.
            right. apply elem_of_list_fmap. exists (delete id G1). split.
            * symmetry. now apply insert_delete.
            * apply IH. replace G with (delete id (<[id:=b]> G)). now apply delete_mono. now apply delete_insert.
          - apply eq_None_not_Some in NIN'. left. apply IH.
            replace G with (delete id (<[id:=b]> G)). replace G1 with (delete id G1). now apply delete_mono.
            now apply delete_notin. now apply delete_insert.
      }
      + apply Equivalence_PreOrder. apply set_equiv_equivalence.
      + apply Proper_focus_aux.
      + apply com_focus_aux.
Qed.

Lemma focus_correct: forall G, forall G1 G2, ((G1, G2) ∈ (focus G)) <-> focus_sem G G1 G2.
Proof.
  intros *. unfold focus. split.
  - intros H. apply elem_of_list_fmap in H as (P & EQ & H).
    unfold focus_aux2 in EQ. apply pair_equal_spec in EQ as [<- ->].
    apply focus_aux_correct in H as SUB.
    split.
    * now apply map_disjoint_difference_r.
    * now apply map_difference_union.
  - intros [PART <-]. apply elem_of_list_fmap. unfold focus_aux2. exists G1.
    split. apply pair_equal_spec. split; trivial.
    * simplify_map_eq. eapply map_union_cancel_l. symmetry. apply PART. apply map_disjoint_difference_l.
      apply map_union_subseteq_l. symmetry. apply map_difference_union. apply map_union_subseteq_l.
    * apply focus_aux_correct. apply map_union_subseteq_l.
Qed.