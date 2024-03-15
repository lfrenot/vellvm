From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule MapCFG Head Focus Patterns.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Patterns.

Definition is_seq (A B: blk) := match successors A with
  | [x] => eqb x B.(blk_id)
  | _ => false
end.

Definition DoubleHead {S} (P: Pat S) := 
  (Head (Head P)) when (fun '(A,(B,_)) => is_seq A B).

Definition BlockFusion {S} (P: Pat S) :=
  (Focus (DoubleHead P)) when (fun '(G,(_,(B,_))) => is_empty (predecessors B.(blk_id) G)).

Lemma is_seq_correct:
  forall A B, is_seq A B = true <->
  successors A = [B.(blk_id)].
Proof.
  unfold is_seq. intros A B. split; intro H.
  induction (successors A) as [|a l IHl]. discriminate. induction l.
  apply eqb_eq in H. now subst. discriminate.
  rewrite H. now apply eqb_eq.
Qed.

Definition DoubleHead_sem A B G G' := let G'' := (add B.(blk_id) B G') in
  successors A = [B.(blk_id)] /\
  (predecessors B.(blk_id) G) ≡ (add A.(blk_id) A empty) /\
  G ≡ (add A.(blk_id) A G'') /\
  is_head G G'' A /\ is_head G'' G' B.

Theorem DoubleHead_correct {S}: forall A B G (P:Pat S) X,
  wf_map_cfg G -> (A,(B,X)) ∈ (MatchAll (DoubleHead P) G) <->
  exists G', X ∈ (MatchAll P G') /\ DoubleHead_sem A B G G'.
Proof.
  intros A B G P X Hwf. unfold DoubleHead. split.
  - intro H.
    apply pat_when_correct in H as [H HWhen].
    apply pat_head_correct in H as [G1 [[HRA [HwfA [HMA HPA]]] H]]; trivial.
    apply pat_head_correct in H as [G2 [[HRB [HwfB [HMB HPB]]] H]]; trivial.
    apply is_seq_correct in HWhen.
    exists G2. split; trivial.
    repeat split; trivial.
    * apply add_predecessor; trivial. eapply Empty_m. unfold predecessors.
      eapply fold_Equal; auto.
      + symmetry. apply HRA.
      + trivial.
    * apply add_remove_elim2. trivial.
      etransitivity. 2:apply HRA.
      symmetry. now apply add_remove_elim2.
    * etransitivity. 2:apply HRA. symmetry. now apply add_remove_elim2.
    * eapply wf_map_cfg_eq. 2:apply HwfA. now apply add_remove_elim2.
    * etransitivity. apply HRB. apply remove_m. reflexivity. now apply add_remove_elim2.
    * apply add_1. reflexivity.
    * eapply Empty_m. 2: apply HPB. unfold predecessors. apply fold_Equal; auto.
      symmetry. now apply add_remove_elim2.
  - intros [G' [HG' [Hs [Hp [He [HhA HhB]]]]]].
    apply pat_when_correct. split. apply pat_head_correct; trivial.
    exists (add (blk_id B) B G'). split. trivial.
    apply pat_head_correct. apply add_wf_map_cfg. destruct HhB as [HB1 [HB2 [HB3 HB4]]]. trivial.
    exists G'. split; trivial.
    unfold is_seq. rewrite Hs. now apply eqb_eq.
Qed.

Definition BlockFusion_sem A B G G' G'' := let G2 := (add A.(blk_id) A (add B.(blk_id) B G')) in
  (predecessors B.(blk_id) G) ≡ (add A.(blk_id) A empty) /\
  Partition G G'' G2 /\ DoubleHead_sem A B G2 G'.

Theorem BlockFusion_correct {S}: forall A B G G'' (P: Pat S) X, wf_map_cfg G ->
  (G'', (A, (B, X))) ∈ (MatchAll (BlockFusion P) G) <->
  exists G', X ∈ (MatchAll P G') /\ BlockFusion_sem A B G G' G''.
Proof.
  unfold BlockFusion.
  intros A B G G'' P X Hwf. split.
  - intro H. unfold BlockFusion_sem.
    apply pat_when_correct in H as [H HWhen].
    apply pat_focus_correct in H as [G0 [[HPart [Hwf'' Hwf0]] H]]; trivial.
    apply DoubleHead_correct in H as [G' [ HG' [HS [HP [HG0 [HhA HhB]]]]]]; trivial.
    exists G'. split; trivial.
    remember (add (blk_id A) A (add (blk_id B) B G')) as G2. 
    split. 2:split. 3:split; trivial. 3:split. 4:split. 5:split;trivial.
    * unfold predecessors. etransitivity.
    2:apply HP. etransitivity. 2: {
      unfold predecessors. eapply fold_Equal2; auto. reflexivity.
      apply Eempty. apply is_empty_iff. apply HWhen.
    }
    unfold predecessors. apply Partition_fold; auto. now apply Partition_sym.
    * eapply Partition_m. reflexivity. reflexivity. symmetry. apply HG0. trivial.
    * etransitivity. 2:apply HP. unfold predecessors. symmetry. apply fold_Equal;auto.
    * rewrite HeqG2. reflexivity.
    * eapply is_head_eq. apply HG0. reflexivity. trivial.
  - intros [G' [HG' [Hpred [Hpart HDouble]]]].
    remember (add (blk_id A) A (add (blk_id B) B G')) as G2.
    apply pat_when_correct. split.
    apply pat_focus_correct; trivial.
    exists G2. split.
    destruct HDouble as [HSucc [HPred2 [_ [HhA HhB]]]].
    split; trivial. eapply wf_map_cfg_part. apply Hpart. trivial.
    apply DoubleHead_correct. eapply wf_map_cfg_part. apply Hpart. trivial.
    exists G'. split; trivial.
    apply is_empty_1. intros k e H.
    induction (eq_dec k A.(blk_id)) as [a|a].
    * apply eq_eq in a. subst k.
      destruct Hpart as [HD HM].
      eapply HD. split. 2:{ rewrite HeqG2. apply add_in_iff. left. reflexivity. }
      eapply predecessors_in. apply in_mapsto_iff. exists e. apply H.
    * destruct HDouble as [Hsucc [Hpred2 HDouble]].
      assert (Hn: In k (predecessors (blk_id B) G)).
      eapply In_m. reflexivity.
      assert (Heq: (predecessors (blk_id B) G) ≡
                   (fold (predecessors_aux (B.(blk_id))) G''
                         (fold (predecessors_aux (B.(blk_id))) G2 empty))
             ).
      unfold predecessors.
      apply Partition_fold; auto.
      apply Heq. apply predecessors_aux_empty_acc. apply in_mapsto_iff. now exists e.
      eapply empty_in_iff.
      eapply add_neq_in_iff. apply neq_sym. apply a.
      eapply In_m. reflexivity. symmetry. apply Hpred. trivial. 
Qed.

(* Theorem FusionCorrect (G G' G'':map_cfg) A B f to:
  wf_map_cfg G -> to <> B.(blk_id) -> f <> A.(blk_id) ->
  (G'', (A, (B, G'))) ∈ (MatchAll (BlockFusion □) G) ->
  denotation_map_cfg G (f, to) ≈
  denotation_map_cfg (update (update G G') (single (fusion A B))) (f, to).
Admitted. *)