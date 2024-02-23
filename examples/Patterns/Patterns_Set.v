From Vellvm Require Import Syntax ScopeTheory.
From Patterns Require Import IdModule.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.

(* cfg definition *)


Module Map := FMapAVL.Make(IdOT).

Module MapF := FMapFacts.OrdProperties Map.
Import MapF.P.
Import MapF.P.F.

Notation blk := (block dtyp).
Notation bid := block_id.
Notation ocfg := (ocfg dtyp).

Notation mcfg := (Map.t blk).

Definition wf_mcfg (g: mcfg) := forall id b, Map.MapsTo id b g -> b.(blk_id) = id.

(* Correction of wf_mcfg *)

Lemma add_wf_mcfg: forall b g, wf_mcfg g -> wf_mcfg (Map.add b.(blk_id) b g).
Proof.
  intros b g Hwf id a H.
  apply add_mapsto_iff in H. destruct H as [[H1 H2]|[H1 H2]].
  - apply IdOT.eq_eq in H1. now subst a.
  - now apply Hwf.
Qed.

(* Pattern definition *)

Inductive Pat : Type -> Type :=
  | Graph: Pat mcfg
  | When: forall S, Pat S -> (S -> bool) -> Pat S
  | Head: forall S, Pat S -> Pat (blk * S)
  .

(* Head Functions *)

Definition predecessors (b : bid) (G : mcfg) : list bid :=
    Map.fold (fun id bk acc => if is_predecessor b bk then id :: acc else acc) G [].

Definition find_heads_aux (G: mcfg) id b acc : list (blk*mcfg) := match predecessors id G with
  | [] => (b, Map.remove id G)::acc
  | _ => acc
end.

Definition find_heads (G: mcfg): list (blk*mcfg) := Map.fold (find_heads_aux G) G [].

(* Match Functions *)

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
    | _ => []
end.

(* Correction of find_heads *)

(* Search Map.fold. *)

Lemma head_aux_correct1: forall G id b acc, predecessors id G = [] -> In (b, Map.remove id G) (find_heads_aux G id b acc).
Proof.
  intros G id b acc Hp. unfold find_heads_aux. rewrite Hp. now left.
Qed.

Definition head_correct_P1 (G: mcfg): Prop := forall G' b, wf_mcfg G -> In (b, G') (find_heads G) -> Map.remove b.(blk_id) G = G' /\ Map.MapsTo b.(blk_id) b G /\ (predecessors b.(blk_id) G = []).

Lemma head_correct1: forall G, head_correct_P1 G.
Proof.
  apply map_induction;unfold head_correct_P1; intros.
  - assert (H':find_heads m = []). apply fold_Empty. apply eq_equivalence. trivial.
    contradict H1. rewrite H'. now cbn.
  - repeat split.
    * unfold find_heads in H3. apply in_split in H3.
Abort.

(* Lemma head_rec_correct2: forall G G' L b, In (b, G') (find_heads_rec G L) -> exists id, In (id, b) L.
Proof.
  intros G G' L. induction L as [| (ida, a) L IHL]. contradiction.
  cbn. intros b H. induction (predecessors ida G). destruct H as [|].
  - apply pair_equal_spec in H as [H H0]. subst b. exists ida. now left.
  - assert (Hid: exists id, In (id,b) L) by (now apply IHL). destruct Hid as [id Hid]. exists id. now right.
  - assert (Hid: exists id, In (id,b) L) by (now apply IHL). destruct Hid as [id Hid]. exists id. now right.
Qed.

Lemma head_rec_correct3: forall G G' L b id, In (b, G') (find_heads_rec G L) -> In (id, b) L -> predecessors id G = [].
Proof.
  intros G G' L. induction L as [|(ida,a) L IHL]. contradiction.
  cbn. intros b id H HL.
  induction (predecessors ida G). destruct H as [|].
  - apply pair_equal_spec in H. destruct H as [H0 H1].
    destruct HL as [|].  *)
