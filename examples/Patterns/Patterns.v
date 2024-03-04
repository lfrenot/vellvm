From Vellvm Require Import Syntax ScopeTheory.
From Patterns Require Import IdModule.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.

(* cfg definition *)


Module Map := FMapAVL.Make(IdOT).

Module MapF := FMapFacts.OrdProperties Map.
(* Import MapF.P. *)
(* Import MapF.P.F. *)

Notation blk := (block dtyp).
Notation bid := block_id.
Notation ocfg := (ocfg dtyp).

Notation mcfg := (Map.t blk).

Definition wf_mcfg (g: mcfg) := forall id b, Map.MapsTo id b g -> b.(blk_id) = id.

(* Correction of wf_mcfg *)

Lemma add_wf_mcfg: forall b g, wf_mcfg g -> wf_mcfg (Map.add b.(blk_id) b g).
Proof.
  intros b g Hwf id a H.
  apply MapF.P.F.add_mapsto_iff in H. destruct H as [[H1 H2]|[H1 H2]].
  - apply IdOT.eq_eq in H1. now subst a.
  - now apply Hwf.
Qed.

Lemma remove_wf_mcfg: forall id g, wf_mcfg g -> wf_mcfg (Map.remove id g).
Admitted.

(* Pattern definition *)

Inductive Pat : Type -> Type :=
  | Graph: Pat mcfg
  | When: forall S, Pat S -> (S -> bool) -> Pat S
  | Head: forall S, Pat S -> Pat (blk * S)
  | Focus: forall S, Pat S -> Pat (mcfg * S)
  | Map: forall S T, Pat S -> (S -> T) -> Pat T
  .

(* Head Definitions *)

Definition predecessors (b : bid) (G : mcfg) : list bid :=
    Map.fold (fun id bk acc => if is_predecessor b bk then id :: acc else acc) G [].

Definition find_heads_aux (G: mcfg) id b acc : list (blk*mcfg) := match predecessors id G with
  | [] => (b, Map.remove id G)::acc
  | _ => acc
end.

Definition find_heads (G: mcfg): list (blk*mcfg) := Map.fold (find_heads_aux G) G [].

(* Focus Definitions *)

Fixpoint focus_rec (l: list (bid*blk)) (g1: mcfg) (g2: mcfg): list (mcfg*mcfg) :=
  match l with
  | [] => [(g1, g2)]
  | (id,b)::q => focus_rec q g1 g2 ++ focus_rec q (Map.remove id g1) (Map.add id b g2)
end.

Definition focus (G: mcfg):= focus_rec (Map.elements G) G (Map.empty blk).

(* Match Definitions *)

Definition flat_map_r {A B C} (f : B -> list C) :=
  fix flat_map_r (l : list (A*B)) : list (A*C) :=
    match l with
    | [] => []
    | (a, b)::q => map (fun c => (a, c)) (f b)++flat_map_r q
end.

Fixpoint MatchAll {S} (P: Pat S) (g: mcfg) : list S :=
  match P with
    | Graph => [g]
    | Head _ p => flat_map_r (MatchAll p) (find_heads g)
    | Focus _ p => flat_map_r (MatchAll p) (focus g)
    | When _ p f => filter f (MatchAll p g) 
    | Map _ _ p f => map f (MatchAll p g)
    (* | _ => [] *)
end.

(* Correction of find_heads *)

Definition is_head (G G':mcfg) (b:blk) := Map.remove b.(blk_id) G = G' /\ wf_mcfg G' /\ Map.MapsTo b.(blk_id) b G /\ (predecessors b.(blk_id) G = []).

Lemma head_correct: forall G G' b, wf_mcfg G -> (In (b, G') (find_heads G) <-> is_head G G' b).
Admitted.

(* Correction of focus *)

Definition is_focus (G G1 G2: mcfg) := MapF.P.Partition G G1 G2 /\ wf_mcfg G1 /\ wf_mcfg G2.

Lemma focus_correct: forall G G1 G2, wf_mcfg G -> (In (G1, G2) (focus G)) <-> is_focus G G1 G2.
Admitted.

(* Correction de MatchAll *)

Theorem pat_graph_correct: forall G, MatchAll Graph G = [G]. Proof. trivial. Qed.

Lemma map_empty_mapsto: forall (G:mcfg) id b, Map.Empty G -> ~Map.MapsTo id b G.
Proof.
  intros G id b H H0. eapply InA_nil. apply MapF.P.elements_Empty in H. rewrite <-H. apply Map.elements_1. apply H0.
Qed.

Lemma in_flat_map_r {A B C}: forall (f:B->list C) (l:list (A*B)) (a:A) (c:C), In (a,c) (flat_map_r f l) <-> exists b, In (a,b) l /\ In c (f b).
Proof.
  intro f. induction l as [|[a b] l IHl].
  * intros. split. contradiction. intros [b [H1 H2]]. contradiction.
  * intros a' c'. split.
    - cbn. intro H. apply in_app_or in H as [].
      + exists b. apply Coqlib.list_in_map_inv in H as [c'' [H1 H2]]. apply pair_equal_spec in H1 as []. subst a' c''. split.
        ** left. apply pair_equal_spec. split;trivial.
        ** trivial.
      + assert (H': exists b0 : B, In (a', b0) l /\ In c' (f b0)) by now apply IHl.
        destruct H' as [b' [H1 H2]]. exists b'. split; trivial. now right.
    - intros [b' [[H1|H1] H2]];cbn; apply in_or_app.
      + apply pair_equal_spec in H1 as []. subst a' b'. left. now apply in_map.
      + right. apply IHl. now exists b'. 
Qed.

Theorem pat_head_correct {S}: forall (G: mcfg)(P: Pat S) (b:blk) s, wf_mcfg G -> In (b, s) (MatchAll (Head _ P) G) <-> exists G', is_head G G' b /\ In s (MatchAll P G').
Proof.
  intros G P b s Hwf. setoid_rewrite <-head_correct;trivial. apply in_flat_map_r.
Qed.

Theorem pat_focus_correct {S}: forall (G G1: mcfg) (P:Pat S) s, wf_mcfg G -> In (G1, s) (MatchAll (Focus _ P) G) <-> exists G2, is_focus G G1 G2 /\ In s (MatchAll P G2).
Proof.
  intros G G1 P s Hwf. setoid_rewrite <-focus_correct;trivial. apply in_flat_map_r.
Qed.

Theorem pat_when_correct {S}: forall (P: Pat S) f x G, In x (MatchAll (When _ P f) G) <-> In x (MatchAll P G) /\ f x = true.
Proof.
  intros. apply filter_In.
Qed.

Theorem pat_map_correct {S T}: forall (P: Pat S) (f: S -> T) x G, In x (MatchAll (Map _ _ P f) G) <-> exists y, f y = x /\ In y (MatchAll P G).
Proof.
  cbn. intros P f x G. split.
  - intro H. apply Coqlib.list_in_map_inv in H as [y [H1 H2]]. now exists y.
  - intros [y [H1 H2]]. subst x. now apply in_map.
Qed. 