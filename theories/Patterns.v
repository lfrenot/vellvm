(** This file defines [Pattern]s, the [MatchAll] function to interpret them, and correctness proofs. *)

From Vellvm Require Import Syntax.
(* From ITree Require Import ITree Eq. *)
From Pattern Require Import Base Head Focus Block Branch.
(* Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
(* Import ListNotations. *)
Import gmap.
(* Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Branch. *)

(** This section defines the [Pattern] type and the [MatchAll] function to interpret them. *)

Inductive Pattern : Type -> Type :=
  | Graph: Pattern ocfg
  | When: forall {S}, Pattern S -> (S -> bool) -> Pattern S
  | Head: forall {S}, Pattern S -> Pattern (bid * blk * S)
  | Focus: forall {S}, Pattern S -> Pattern (ocfg * S)
  | Map: forall {S} {T}, Pattern S -> (S -> T) -> Pattern T
  | Block: forall {S}, Pattern S -> Pattern (bid * blk * S)
  | Branch: forall {S}, Pattern S -> Pattern (bid * blk * S)
.

Notation "□" := Graph.
Notation "P 'when' b" := (When P b) (at level 45).

Fixpoint flat_map_r {A B C} (f : B -> list C) (l : list (A*B)) : list (A*C) :=
    match l with
    | [] => []
    | (a, b)::q => ((fun c => (a, c)) <$> (f b))++flat_map_r f q
end.

Fixpoint MatchAll {S} (P: Pattern S) (g: ocfg) : list S :=
  match P with
    | □ => [g]
    | Head _ p => flat_map_r (MatchAll p) (heads g)
    | Focus _ p => flat_map_r (MatchAll p) (focus g)
    | p when f => filter (fun x => f x = true) (MatchAll p g) 
    | Map _ _ p f => f <$> (MatchAll p g)
    | Block _ p => flat_map_r (MatchAll p) (blocks g)
    | Branch _ p => flat_map_r (MatchAll p) (branches g)
end.

(** This section contains the correction (and completeness) proofs of [MatchAll].

    These proofs are done for each pattern separately.
    They enable decontructing each atomic patterns for proof on larger ones. 
    They mostly rely on [in_flat_map_r] and the proofs on each pattern's corresponding function, done in its coresponding file. *)

Lemma in_flat_map_r {A B C}:
  forall (f:B->list C) (l:list (A*B)) (a:A) (c:C), (a,c) ∈ (flat_map_r f l) <->
  exists b, (a,b) ∈ l /\ c ∈ (f b).
Proof.
  intro f. induction l as [|[a b] l IHl].
  * intros. cbn. split. intro H. inversion H. intros [b [H1 H2]]. inversion H1.
  * intros a' c'. split.
    - cbn. intro IN. apply elem_of_app in IN as [IN|IN].
      + exists b. apply elem_of_list_fmap in IN as [c'' [EQ IN]].
        apply pair_equal_spec in EQ as []. subst.
        split; trivial. left.
      + assert (exists b0 : B, (a', b0) ∈ l /\ c' ∈ (f b0)) as [b' [IN1 IN2]] by now apply IHl.
        exists b'. split; trivial. now right.
    - intros [b' [IN1 IN2]]. apply elem_of_cons in IN1 as [EQ|IN1]; cbn; apply elem_of_app; [left|right].
      + apply pair_equal_spec in EQ as []. subst. apply elem_of_list_fmap. now exists c'.
      + apply IHl. now exists b'. 
Qed.

Theorem Pattern_Graph_correct: forall G G', G' ∈ (MatchAll □ G) <-> G' = G.
Proof.
  cbn. intros G G'. split; intro; set_solver.
Qed.

Theorem Pattern_Head_correct {S}:
  forall (G: ocfg) (P: Pattern S) id b X,
  (id, b, X) ∈ (MatchAll (Head P) G) <->
  exists G', heads_sem G G' id b /\ X ∈ (MatchAll P G').
Proof.
  intros *. setoid_rewrite <- heads_correct;trivial. apply in_flat_map_r.
Qed.

Theorem Pattern_Focus_correct {S}:
  forall (G G1: ocfg) (P:Pattern S) X, 
  (G1, X) ∈ (MatchAll (Focus P) G) <-> exists G2, focus_sem G G1 G2 /\ X ∈ (MatchAll P G2).
Proof.
  intros *. setoid_rewrite <-focus_correct;trivial. apply in_flat_map_r.
Qed.

Theorem Pattern_When_correct {S}:
  forall (P: Pattern S) f X G,
  X ∈ (MatchAll (P when f) G) <-> f X = true /\ X ∈ (MatchAll P G).
Proof.
  intros. cbn. now rewrite elem_of_list_filter.
Qed.

Theorem Pattern_Map_correct {S T}:
  forall (P: Pattern S) (f: S -> T) X G,
  X ∈ (MatchAll (Map P f) G) <-> exists y, X = f y /\ y ∈ (MatchAll P G).
Proof.
  cbn. intros P f X G. now rewrite elem_of_list_fmap.
Qed.

Theorem Pattern_Block_correct {S}:
  forall (G: ocfg) (P: Pattern S) id (b:blk) X,
  (id, b, X) ∈ (MatchAll (Block P) G) <->
  exists G', blocks_sem G G' id b /\ X ∈ (MatchAll P G').
Proof.
  intros. setoid_rewrite <-blocks_correct;trivial. apply in_flat_map_r.
Qed.

Theorem Pattern_Branch_correct {S}:
  forall G P B id (s:S),
  (id,B,s) ∈ (MatchAll (Branch P) G) <->
  exists G', branch_sem G G' id B /\ s ∈ (MatchAll P G').
Proof.
  intros. setoid_rewrite <-branches_correct; trivial. apply in_flat_map_r.
Qed.