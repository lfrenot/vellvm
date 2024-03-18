From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule MapCFG Head Focus Block.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block.

(* Pattern definition *)

Inductive Pat : Type -> Type :=
  | Graph: Pat map_cfg
  | When: forall {S}, Pat S -> (S -> bool) -> Pat S
  | Head: forall {S}, Pat S -> Pat (blk * S)
  | Focus: forall {S}, Pat S -> Pat (map_cfg * S)
  | Map: forall {S} {T}, Pat S -> (S -> T) -> Pat T
  | Block: forall {S}, Pat S -> Pat (blk * S)
.

Notation "□" := Graph.
Notation "P 'when' b" := (When P b) (at level 45).

(* Match Definitions *)

Definition flat_map_r {A B C} (f : B -> list C) :=
  fix flat_map_r (l : list (A*B)) : list (A*C) :=
    match l with
    | [] => []
    | (a, b)::q => List.map (fun c => (a, c)) (f b)++flat_map_r q
end.

Lemma in_flat_map_r {A B C}:
  forall (f:B->list C) (l:list (A*B)) (a:A) (c:C), (a,c) ∈ (flat_map_r f l) <->
  exists b, (a,b) ∈ l /\ c ∈ (f b).
Proof.
  intro f. induction l as [|[a b] l IHl].
  * intros. split. contradiction. intros [b [H1 H2]]. contradiction.
  * intros a' c'. split.
    - cbn. intro H. apply in_app_or in H as [].
      + exists b.
        apply Coqlib.list_in_map_inv in H as [c'' [H1 H2]].
        apply pair_equal_spec in H1 as [].
        subst.
        split; trivial. left. apply pair_equal_spec. now split.
      + assert (H': exists b0 : B, (a', b0) ∈ l /\ c' ∈ (f b0)) by now apply IHl.
        destruct H' as [b' [H1 H2]]. exists b'. split; trivial. now right.
    - intros [b' [[H1|H1] H2]];cbn; apply in_or_app.
      + apply pair_equal_spec in H1 as []. subst. left. now apply in_map.
      + right. apply IHl. now exists b'. 
Qed.

Fixpoint MatchAll {S} (P: Pat S) (g: map_cfg) : list S :=
  match P with
    | □ => [g]
    | Head _ p => flat_map_r (MatchAll p) (heads g)
    | Focus _ p => flat_map_r (MatchAll p) (focus g)
    | p when f => List.filter f (MatchAll p g) 
    | Map _ _ p f => List.map f (MatchAll p g)
    | Block _ p => flat_map_r (MatchAll p) (blocks g)
end.

(* Correction de MatchAll *)

Theorem Pat_Graph_correct: forall G G', G' ∈ (MatchAll □ G) -> G' = G.
Proof.
  cbn. intros G G' H. destruct H; now destruct H.
Qed.

Theorem Pat_Head_correct {S}:
  forall (G: map_cfg) (P: Pat S) (b:blk) s, wf_map_cfg G ->
  (b, s) ∈ (MatchAll (Head P) G) <->
  exists G', is_head G G' b /\ s ∈ (MatchAll P G').
Proof.
  intros G P b s Hwf. setoid_rewrite <- heads_correct;trivial. apply in_flat_map_r.
Qed.

Theorem Pat_Focus_correct {S}:
  forall (G G1: map_cfg) (P:Pat S) s, wf_map_cfg G ->
  (G1, s) ∈ (MatchAll (Focus P) G) <-> exists G2, is_focus G G1 G2 /\ s ∈ (MatchAll P G2).
Proof.
  intros G G1 P s Hwf. setoid_rewrite <-focus_correct;trivial. apply in_flat_map_r.
Qed.

Theorem Pat_When_correct {S}:
  forall (P: Pat S) f x G,
  x ∈ (MatchAll (When P f) G) <-> x ∈ (MatchAll P G) /\ f x = true.
Proof.
  intros. apply filter_In.
Qed.

Theorem Pat_Map_correct {S T}:
  forall (P: Pat S) (f: S -> T) x G,
  x ∈ (MatchAll (Map P f) G) <-> exists y, f y = x /\ y ∈ (MatchAll P G).
Proof.
  cbn. intros P f x G. split.
  - intro H. apply Coqlib.list_in_map_inv in H as [y [H1 H2]]. now exists y.
  - intros [y [H1 H2]]. subst x. now apply in_map.
Qed.

Theorem Pat_Block_correct {S}:
  forall (G: map_cfg) (P: Pat S) (b:blk) s, wf_map_cfg G ->
  (b, s) ∈ (MatchAll (Block P) G) <->
  exists G', is_block G G' b /\ s ∈ (MatchAll P G').
Proof.
  intros. setoid_rewrite <-blocks_correct;trivial. apply in_flat_map_r.
Qed.

Definition map_cfg_to_ocfg: map_cfg -> ocfg. Admitted.

(* Definition denotation_map_cfg: map_cfg -> bid * bid -> ITreeDefinition.itree instr_E (bid * bid + uvalue). Admitted. *)

Definition fusion (A B: blk): blk. Admitted.

Definition single (B:blk) := add B.(blk_id) B empty.