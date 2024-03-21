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

Definition head_aux_sem (G0 G G': map_cfg) b :=
  G' = (remove_id b G0) /\ wf_map_cfg G' /\
  MapsTo_id b G /\ Empty (predecessors b.(blk_id) G0).

Definition head_sem (G G':map_cfg) (b:blk) := head_aux_sem G G G' b.

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

Lemma head_aux_sem_eq: forall G0 G G' G1 b, G' ≡ G -> head_aux_sem G0 G G1 b <-> head_aux_sem G0 G' G1 b.
Proof.
  intros GO G G' G1 b Heq. assert (Heq': G ≡ G') by now symmetry.
  split; intros [H1 [Hwf1 [Hb Hp]]]; repeat split; trivial;
  eapply MapsTo_m; try apply Heq; try apply Heq'; try reflexivity; trivial.
Qed.

Lemma heads_aux_correct:
  forall G G0 G' b, wf_map_cfg G -> wf_map_cfg G0 ->
  (b, G') ∈ (fold (heads_aux G0) G []) <-> head_aux_sem G0 G G' b.
Proof.
  intros G G0. apply fold_rec_bis.
  - intros G1 G2 a Heq Hrec G' B Hwf2 Hwf0. setoid_rewrite head_aux_sem_eq. 2:apply Heq.
    apply Hrec; [apply (wf_map_cfg_eq G2)|];trivial. now symmetry.
  - intros. split. try contradiction. intros [_ [_ [Hb _]]].
    now apply empty_mapsto_iff in Hb.
  - intros idB B a G1 HB HnI Hrec G2 A Hwfa Hwf0.
    assert (HidB: B.(blk_id) = idB). apply Hwfa. now apply add_1. subst idB.
    split.
    * unfold heads_aux. remember (is_empty (predecessors B.(blk_id) G0)) as b. induction b. intros [H|H].
      + apply pair_equal_spec in H as [H1 H2].
        subst A G2. repeat split; trivial.
        -- now apply remove_wf_map_cfg.
        -- now apply add_1.
        -- now apply is_empty_iff.
      + assert (Hh1: (head_aux_sem G0 G1 G2 A)). { 
          apply Hrec; trivial.
          eapply wf_map_cfg_eq. 2: {apply remove_wf_map_cfg. apply Hwfa. } symmetry. apply remove_add_elim1; trivial.
        } destruct Hh1 as [H2 [Hwf2 [HA Hp]]]. repeat split; trivial.
        case (eq_dec A.(blk_id) B.(blk_id)); unfold eq; intro He.
        -- contradict HnI. exists A. apply eq_eq in He. now rewrite <- He.
        -- eapply add_2. now apply neq_sym. trivial.
      + intro H. assert (Hh1: (head_aux_sem G0 G1 G2 A)). { 
          apply Hrec; trivial.
          eapply wf_map_cfg_eq. 2: {apply remove_wf_map_cfg. apply Hwfa. } symmetry. apply remove_add_elim1; trivial.
        } destruct Hh1 as [H2 [Hwf2 [HA Hp]]]. repeat split; trivial.
        case (eq_dec A.(blk_id) B.(blk_id)); unfold eq; intro He.
        -- contradict HnI. exists A. apply eq_eq in He. now rewrite <- He.
        -- eapply add_2. now apply neq_sym. trivial.
    * intros [H2 [Hwf2 [HA Hp]]]. unfold heads_aux.
      remember (is_empty (predecessors B.(blk_id) G0)) as b. induction b.
      case (eq_dec A.(blk_id) B.(blk_id)); unfold eq; intro H. left.
      assert (HAB: A=B). {
        eapply MapsTo_fun. apply HA. apply eq_eq in H. rewrite H. now apply add_1.
      }
      + now subst.
      + right. apply Hrec. eapply wf_map_cfg_add. apply HnI. apply Hwfa. trivial.
         repeat split; trivial. eapply add_3. apply neq_sym. apply H. apply HA.
      + apply Hrec. eapply wf_map_cfg_add. apply HnI. apply Hwfa. trivial.
         repeat split; trivial. case (eq_dec A.(blk_id) B.(blk_id)); unfold eq; intro H.
         -- assert (HAB: A=B). {
              eapply MapsTo_fun. apply HA. apply eq_eq in H. rewrite H. now apply add_1.
            } subst A. apply is_empty_iff in Hp. rewrite Hp in Heqb. discriminate.
         -- eapply add_3. apply neq_sym. apply H. apply HA.
Qed.

Lemma heads_correct:
  forall G G' b, wf_map_cfg G ->
  (b, G') ∈ (heads G) <-> head_sem G G' b.
Proof.
  intros. now apply heads_aux_correct.
Qed.