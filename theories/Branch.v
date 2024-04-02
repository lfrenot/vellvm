From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Pattern Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.

Definition branches_aux (G: map_cfg) id b acc : list (blk*bid*bid*map_cfg) := match b.(blk_term) with
  | TERM_Br _ l r => (b, l, r, (remove id G))::acc
  | _ => acc
end.

Definition branches (G: map_cfg): list (blk*bid*bid*map_cfg) := fold (branches_aux G) G [].

Record branch_aux_sem (G0 G G': map_cfg) (B: blk) l r := {
  EQ: G' = (remove_id B G0);
  BR: exists e, B.(blk_term) = TERM_Br e l r;
  MT: MapsTo_id B G
}.

Definition branch_sem G G' B l r := branch_aux_sem G G G' B l r.

Lemma branches_aux_correct:
  forall G0 G G' b l r, wf_map_cfg G ->
  (b, l , r, G') ∈ (fold (branches_aux G0) G []) <-> branch_aux_sem G0 G G' b l r.
Proof.
  intros G0 G. apply fold_rec_bis.
  - intros * EQ REC * WF'. assert (WF: wf_map_cfg m) by now apply (wf_map_cfg_eq m'). split.
    * intros IN.
      apply REC in IN as [EQ' [e TERM] MT]; trivial. repeat split; trivial.
      now exists e. eapply MapsTo_m. 4: apply MT. reflexivity. trivial. now symmetry.
    * intros [EQ' [e TERM] MT]. apply REC; trivial. repeat split; trivial. now exists e.
      eapply MapsTo_m. 4: apply MT. all: auto. reflexivity.
  - intros * WF. split. intro H. destruct H.
    intros [EQ' [e TERM] MT]. now apply empty_mapsto_iff in MT.
  - intros idB B * MT NIN REC * WFa.
    assert (H: B.(blk_id) = idB). { apply WFa. now apply add_1. }
    assert (WF': wf_map_cfg m'). { eapply add_wf_map_cfg. apply NIN. apply WFa. }
    subst. split. 
    * unfold branches_aux. intros IN. remember B.(blk_term) as T. induction T.
      3: destruct IN as [EQ|IN].
      3: {
        apply pair_equal_spec in EQ as [EQ EQG].
        apply pair_equal_spec in EQ as [EQ EQ1].
        apply pair_equal_spec in EQ as [EQ EQ2]. subst.
        repeat split; trivial. exists v. now rewrite HeqT.
        now apply add_1. 
      }
      all: apply REC in IN as [EQ' [e TERM] MT']; trivial.
      all: repeat split; trivial; [now exists e|].
      all: apply add_2; [|apply MT'].
      all: intros EQ; apply NIN; exists b.
      all: apply eq_eq in EQ; rewrite EQ; apply MT'.
    * intros [EQ' [e TERM] MT']. apply add_mapsto_iff in MT' as [[EQid EQb]|[NEQ MT']].
      + subst b. unfold branches_aux. rewrite TERM. subst. now left.
      + unfold branches_aux. remember B.(blk_term) as T. induction T.
        3: right.
        all: apply REC; trivial. all: split; trivial; now exists e.
Qed.

Lemma branches_correct:
  forall G G' b l r, wf_map_cfg G ->
  (b,l,r,G') ∈ (branches G) <-> branch_sem G G' b l r.
Proof.
  intros. now apply branches_aux_correct.
Qed.