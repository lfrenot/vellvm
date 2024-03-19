From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Pattern Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.

Definition branches_aux (G: map_cfg) id b acc : list (blk*bid*bid*map_cfg) := match b.(blk_term) with
    | TERM_Br _ l r => (b, l, r, (remove id (remove l (remove r G))))::acc
    | _ => acc
end.

Definition branches (G: map_cfg): list (blk*bid*bid*map_cfg) := fold (branches_aux G) G [].

Definition is_branch (G G': map_cfg) B l r :=
    exists e L R, MapsTo_id B G /\ MapsTo l L G /\ MapsTo r R G /\
    G' ≡ (remove_id B (remove l (remove r G))) /\ B.(blk_term) = TERM_Br e l r.

Lemma branches_correct:
    forall G G' b l r, wf_map_cfg G ->
    ((b,l,r, G') ∈ (branches G) <-> is_branch G G' b l r).
Proof.
Admitted.