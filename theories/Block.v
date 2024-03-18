From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Pattern Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.


Definition blocks_aux (G: map_cfg) : _ -> (blk*map_cfg) := fun '(id, b) => (b, remove id G).

Definition blocks (G: map_cfg): list (blk*map_cfg) := List.map (blocks_aux G) (elements G).

Definition is_block (G G': map_cfg) b := MapsTo b.(blk_id) b G /\ G' ≡ (remove b.(blk_id) G).

Lemma blocks_correct: forall G G' b, wf_map_cfg G -> ((b, G') ∈ (blocks G) <-> is_block G G' b).
Proof.
Admitted.