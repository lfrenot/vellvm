(** This file defines [Pattern]s, the [MatchAll] function to interpret them, and correctness proofs. *)

From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule MapCFG Head Focus Block Branch.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Branch.

(** This scetionc defines the [Pattern] type and the [MatchAll] function to interpret them. *)

Inductive Pattern : Type -> Type :=
  | Graph: Pattern map_cfg
  | When: forall {S}, Pattern S -> (S -> bool) -> Pattern S
  | Head: forall {S}, Pattern S -> Pattern (blk * S)
  | Focus: forall {S}, Pattern S -> Pattern (map_cfg * S)
  | Map: forall {S} {T}, Pattern S -> (S -> T) -> Pattern T
  | Block: forall {S}, Pattern S -> Pattern (blk * S)
  | Branch: forall {S}, Pattern S -> Pattern (blk * bid * bid * S)
.

Notation "□" := Graph.
Notation "P 'when' b" := (When P b) (at level 45).

Definition flat_map_r {A B C} (f : B -> list C) :=
  fix flat_map_r (l : list (A*B)) : list (A*C) :=
    match l with
    | [] => []
    | (a, b)::q => List.map (fun c => (a, c)) (f b)++flat_map_r q
end.

Fixpoint MatchAll {S} (P: Pattern S) (g: map_cfg) : list S :=
  match P with
    | □ => [g]
    | Head _ p => flat_map_r (MatchAll p) (heads g)
    | Focus _ p => flat_map_r (MatchAll p) (focus g)
    | p when f => List.filter f (MatchAll p g) 
    | Map _ _ p f => List.map f (MatchAll p g)
    | Block _ p => flat_map_r (MatchAll p) (blocks g)
    | Branch _ p => flat_map_r (MatchAll p) (branches g)
end.

(** This section contains the correction (and completeness) proofs of [MatchAll].

    These proofs are done for each pattern separately.
    They enable decontructing each atomic patterns for proof on larger ones. 
    They mostly rely on [in_flat_map_r] and the proofs on each pattern's corresponding function, done in it's coresponding file. *)

Lemma in_flat_map_r {A B C}:
  forall (f:B->list C) (l:list (A*B)) (a:A) (c:C), (a,c) ∈ (flat_map_r f l) <->
  exists b, (a,b) ∈ l /\ c ∈ (f b).
Proof.
  intro f. induction l as [|[a b] l IHl].
  * intros. split. contradiction. intros [b [H1 H2]]. contradiction.
  * intros a' c'. split.
    - cbn. intro IN. apply in_app_or in IN as [IN|IN].
      + exists b.
        apply Coqlib.list_in_map_inv in IN as [c'' [EQ IN]].
        apply pair_equal_spec in EQ as []. subst.
        split; trivial. left. apply pair_equal_spec. now split.
      + assert (H': exists b0 : B, (a', b0) ∈ l /\ c' ∈ (f b0)) by now apply IHl.
        destruct H' as [b' [IN1 IN2]]. exists b'. split; trivial. now right.
    - intros [b' [[EQ|IN1] IN2]];cbn; apply in_or_app.
      + apply pair_equal_spec in EQ as []. subst. left. now apply in_map.
      + right. apply IHl. now exists b'. 
Qed.

Theorem Pattern_Graph_correct: forall G G', G' ∈ (MatchAll □ G) -> G' = G.
Proof.
  cbn. intros G G' H. destruct H; now destruct H.
Qed.

Theorem Pattern_Head_correct {S}:
  forall (G: map_cfg) (P: Pattern S) (b:blk) X, wf_map_cfg G ->
  (b, X) ∈ (MatchAll (Head P) G) <->
  exists G', heads_sem G G' b /\ X ∈ (MatchAll P G').
Proof.
  intros G P b X WF. setoid_rewrite <- heads_correct;trivial. apply in_flat_map_r.
Qed.

Theorem Pattern_Focus_correct {S}:
  forall (G G1: map_cfg) (P:Pattern S) X, wf_map_cfg G ->
  (G1, X) ∈ (MatchAll (Focus P) G) <-> exists G2, focus_sem G G1 G2 /\ X ∈ (MatchAll P G2).
Proof.
  intros G G1 P X WF. setoid_rewrite <-focus_correct;trivial. apply in_flat_map_r.
Qed.

Theorem Pattern_When_correct {S}:
  forall (P: Pattern S) f X G,
  X ∈ (MatchAll (P when f) G) <-> X ∈ (MatchAll P G) /\ f X = true.
Proof.
  intros. apply filter_In.
Qed.

Theorem Pattern_Map_correct {S T}:
  forall (P: Pattern S) (f: S -> T) X G,
  X ∈ (MatchAll (Map P f) G) <-> exists y, f y = X /\ y ∈ (MatchAll P G).
Proof.
  cbn. intros P f X G. split.
  - intro H. apply Coqlib.list_in_map_inv in H as [y [H1 H2]]. now exists y.
  - intros [y [H1 H2]]. subst. now apply in_map.
Qed.

Theorem Pattern_Block_correct {S}:
  forall (G: map_cfg) (P: Pattern S) (b:blk) X, wf_map_cfg G ->
  (b, X) ∈ (MatchAll (Block P) G) <->
  exists G', blocks_sem G G' b /\ X ∈ (MatchAll P G').
Proof.
  intros. setoid_rewrite <-blocks_correct;trivial. apply in_flat_map_r.
Qed.