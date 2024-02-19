From Vellvm Require Import Syntax ScopeTheory.
Require Import List.
Import ListNotations.

Notation graph := (ocfg dtyp).
Notation blk := (block dtyp).

Inductive Pat : Type -> Type :=
  | Graph: Pat graph
  | When: forall S, Pat S -> (S -> bool) -> Pat S
  | Head: forall S, Pat S -> (S -> graph) -> Pat (blk * graph)
  | Seq: forall S, Pat S -> (S -> graph) -> Pat (graph * graph)
  | Cart: forall S1 S2, Pat S1 -> Pat S2 -> Pat (S1 * S2)
  (* | Loop: Pat T (graph * graph * graph) *)
  .

Definition eqb_bid b b' :=
  match b,b' with
    | Name s, Name s' => String.eqb s s'
    | Anon n, Anon n' => @RelDec.eq_dec int eq_dec_int n n'
    | Raw n, Raw n' => @RelDec.eq_dec int eq_dec_int n n'
    | _ , _ => false
end.

Fixpoint remove_blk (B : blk) (G : graph) :=
  match G with
  | [] => []
  | A::G' => if (eqb_bid B.(blk_id) A.(blk_id)) then remove_blk B G' else A::(remove_blk B G')
end.

Fixpoint find_heads_rec (G : graph) (next: list blk) : list (blk * graph) :=
  match next with
  | [] => []
  | bk :: next' => match predecessors bk.(blk_id) G with
    | [] => (bk, (remove_blk bk G))::find_heads_rec G next'
    | _ => find_heads_rec G next'
  end
end.

Definition find_heads (G: graph) : list (blk * graph) := find_heads_rec G G.

Fixpoint MatchAll {S} (P: Pat S) (G: graph) : list S :=
  match P with
    | When _ p f => filter f (MatchAll p G)
    | Head _ p f => flat_map find_heads (map f (MatchAll p G))
    | Graph => [G]
    | _ => []
end.

(* Correction of find_heads *)

Lemma find_heads_rec_cons: forall (L G: graph) (A: blk), find_heads_rec G (A::L) = (find_heads_rec G [A]) ++ (find_heads_rec G L).
Proof.
  cbn. intros L G A. induction (predecessors (blk_id A) G); reflexivity.
Qed.

Lemma find_heads_rec_app: forall (L1 L2 G: graph), find_heads_rec G (L1++L2) = (find_heads_rec G L1) ++ (find_heads_rec G L2).
Proof.
  intro L1. induction L1 as [|a L1 IHL1]. trivial.
  intros L2 G. rewrite <-app_comm_cons. rewrite find_heads_rec_cons.
  replace (find_heads_rec G (a :: L1)) with (find_heads_rec G [a] ++ find_heads_rec G (L1)) by (symmetry; apply find_heads_rec_cons).
  rewrite IHL1. apply app_assoc.
Qed.

Lemma head_rec_correct1: forall (G L: graph) (B: blk), In B L -> (predecessors B.(blk_id) G = []) -> In (B, remove_blk B G) (find_heads_rec G L).
Proof.
  intros G L B HL Hp. apply in_split in HL. destruct HL as [l1 [l2 HL]].
  subst L. rewrite find_heads_rec_app. apply in_or_app. right.
  cbn. rewrite Hp. left. trivial.
Qed.

Lemma head_rec_correct2_1: forall G G' L B, In (B, G') (find_heads_rec G L) -> remove_blk B G = G'.
Proof.
  intros G G' L. induction L as [| a L IHL]. contradiction.
  intros B H. rewrite find_heads_rec_cons in H. apply in_app_or in H. destruct H.
  - unfold find_heads_rec in H. induction (predecessors (blk_id a) G).
    * destruct H.
      + apply pair_equal_spec in H. destruct H. subst a. trivial.
      + contradiction.
    * contradiction.
  - apply IHL. trivial.
Qed.

Lemma head_rec_correct2_2: forall G G' L B, In (B, G') (find_heads_rec G L) -> In B L.
Proof.
  intros G G' L. induction L as [|a L IHL]. contradiction.
  cbn. intros B Hh. induction (predecessors (blk_id a) G). destruct Hh as [Hh|Hh].
  - left. apply pair_equal_spec in Hh. destruct Hh. trivial.
  - right. apply IHL. trivial.
  - right. apply IHL. trivial.
Qed.

Lemma head_rec_correct2_3: forall G G' L B, In (B, G') (find_heads_rec G L) -> (predecessors B.(blk_id) G = []).
Proof.
  intros G G' L. induction L as [|a L IHL]. contradiction.
  cbn. intros B Hh.
  assert (Lemme_nul: a=B -> (predecessors (blk_id a) G)=[] -> (predecessors (blk_id B) G) = []) by (intros; subst a; trivial).
  induction (predecessors (blk_id a) G). destruct Hh as [Hh|Hh].
  - apply pair_equal_spec in Hh. destruct Hh as [H0 H1]. apply Lemme_nul;trivial.
  - apply IHL. trivial.
  - apply IHL. trivial.
Qed.

Lemma head_rec_correct: forall G G' L B, In (B, G') (find_heads_rec G L) <-> remove_blk B G = G' /\ In B L /\ (predecessors B.(blk_id) G = []).
Proof.
  intros G G' L. split. intro H. split. 2: split.
  - eapply head_rec_correct2_1. apply H. 
  - eapply head_rec_correct2_2. apply H.
  - eapply head_rec_correct2_3. apply H.
  - intro H. destruct H as [H1 [H2 H3]]. subst G'. apply head_rec_correct1; trivial.
Qed.

Lemma head_correct: forall G G' B, In (B, G') (find_heads G) <-> remove_blk B G = G' /\ In B G /\ (predecessors B.(blk_id) G = []).
Proof.
  intros. apply head_rec_correct.
Qed.

(* Correction of Match *)

Theorem pat_head_correct {S}: forall (P: Pat S) (G G' G'': graph) B f,
  In (B, G') (MatchAll (Head _ P f) G) <-> exists G'', remove_blk B G'' = G' /\ In G'' (map f (MatchAll P G)) /\ In B G'' /\ (predecessors B.(blk_id) G'' = []).
Proof.
  intros. cbn. split; intro H.
  - apply in_flat_map in H. destruct H as [g [H1 H2]]. apply head_rec_correct in H2 as [H2 [H3 H4]]. exists g. repeat split;trivial.
  - destruct H as [g [H1 [H2 [H3 H4]]]]. apply in_flat_map. exists g. split; trivial. apply head_correct. repeat split;trivial.
Qed.

Theorem pat_when_correct {S}: forall (P: Pat S) f x G, In x (MatchAll (When _ P f) G) <-> In x (MatchAll P G) /\ f x = true.
Proof. 
  intros. apply filter_In.
Qed.