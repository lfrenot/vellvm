From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
From Pattern Require Import IdModule MapCFG.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG.

Fixpoint focus_rec l (g1 g2: map_cfg) :=
  match l with
  | [] => [(g1, g2)]
  | (id,b)::q => focus_rec q g1 g2 ++ focus_rec q (remove id g1) (add id b g2)
end.

Definition focus (G: map_cfg) := focus_rec (elements G) G empty.

Record focus_sem (G G1 G2: map_cfg): Prop := {
  PART: Partition G G1 G2; 
  WF1: wf_map_cfg G1;
  WF2: wf_map_cfg G2
}.

Lemma focus_correct: forall G G1 G2, wf_map_cfg G -> ((G1, G2) ∈ (focus G)) <-> focus_sem G G1 G2.
Admitted.