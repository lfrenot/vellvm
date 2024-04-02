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

Record branch_sem (G G': map_cfg) (B:blk) l r: Prop := {
    EQ: G' = (remove_id B G);
    BR: exists e, B.(blk_term) = TERM_Br e l r
}.

Lemma branches_correct:
    forall G G' b l r, wf_map_cfg G ->
    (b,l,r,G') ∈ (branches G) <-> branch_sem G G' b l r.
Proof.
Admitted.