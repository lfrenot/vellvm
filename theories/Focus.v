From Vellvm Require Import Syntax.
(* From ITree Require Import ITree Eq.
Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
(* Import ListNotations. *)
From Pattern Require Import Base.
(* Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG. *)
Import gmap.

Fixpoint focus_rec l (g1 g2: ocfg) :=
  match l with
  | [] => [(g1, g2)]
  | (id,b)::q => focus_rec q g1 g2 ++ focus_rec q (delete id g1) (<[id:=b]> g2)
end.

Definition focus (G: ocfg) := focus_rec (map_to_list G) G ∅.

Record focus_sem (G G1 G2: ocfg): Prop := {
  SUB1: G1 ⊆ G;
  SUB2: G2 ⊆ G;
  PART: G1 ##ₘ G2;
  CUP: G1 ∪ G2 = G
}.

Definition focus_correct_P G := forall G1 G2, ((G1, G2) ∈ (focus G)) <-> focus_sem G G1 G2.

Lemma focus_correct: forall G, forall G1 G2, ((G1, G2) ∈ (focus G)) <-> focus_sem G G1 G2.
Proof.
Admitted.