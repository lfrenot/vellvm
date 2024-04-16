From Vellvm Require Import Syntax Tactics.
(* From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
(* Import ListNotations. *)
From Pattern Require Import Base.
Import gmap.
(* Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG. *)

Definition branches_aux (G: ocfg) id b acc : list (bid*blk*ocfg) := match b.(blk_term) with
  | TERM_Br _ l r => (id, b, (delete id G))::acc
  | _ => acc
end.

Definition branches (G: ocfg): list (bid*blk*ocfg) := map_fold (branches_aux G) [] G.

Record branch_aux_sem (G0 G G': ocfg) id b := {
  EQ: G' = delete id G0;
  BR: exists e l r, b.(blk_term) = TERM_Br e l r;
  IN: G !! id = Some b
}.

Definition branch_sem G G' id b := branch_aux_sem G G G' id b.

Definition branches_aux_P G0 (s:list (bid*blk*ocfg)) G :=
  forall id b G', (id, b, G') ∈ s <-> branch_aux_sem G0 G G' id b.

Lemma branches_aux_correct:
  forall G G0,
  branches_aux_P G0 (map_fold (branches_aux G0) [] G) G.
Proof.
  intros *. apply map_fold_ind; clear G; unfold branches_aux_P.
  - split. intro H. inversion H. intros []. set_solver.
  - intros id b G acc NIN IH id' b' G'. unfold branches_aux. split.
    * intro IN. break_match_hyp. 3: apply elem_of_cons in IN as [EQ|IN].
      3: {
        repeat apply pair_equal_spec in EQ as [EQ ?]. subst.
        split; trivial. now exists v, br1, br2. now simplify_map_eq.
      }
      all: apply IH in IN as []; split; trivial; now simplify_map_eq.
    * intros [EQ (e & l & r & BR) IN]. break_match_goal.
      3: case (decide (id=id')); intros DEC; apply elem_of_cons; [left | right].
      3: {
        subst. pose proof lookup_insert_rev _ _ _ _ IN. subst. rewrite BR in Heqt. inversion Heqt. now subst.
      }
      all: assert (id <> id') by (auto; intro; subst; simplify_map_eq; rewrite BR in Heqt; discriminate).
      all: apply IH; split; trivial; [now exists e, l, r|now simplify_map_eq].
Qed.

Lemma branches_correct:
  forall G G' id b, 
  (id,b,G') ∈ (branches G) <-> branch_sem G G' id b.
Proof.
  intros. now apply branches_aux_correct.
Qed.