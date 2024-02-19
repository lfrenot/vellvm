From Vellvm Require Import Syntax ScopeTheory.
Require Import List.
Import ListNotations.
From Imp2Vir Require Import CFGC_Utils.

Inductive Pat T : Type -> Type :=
    | Head: Pat T (block T * ocfg T)
    | Seq: Pat T (ocfg T * block T * ocfg T).

Fixpoint remove_blk {T} (B : block T) (G : ocfg T) :=
    match G with
    | [] => []
    | A::G' => if (eqb_bid B.(blk_id) A.(blk_id)) then remove_blk B G' else A::(remove_blk B G')
end.

Fixpoint find_heads_rec {T} (G : ocfg T) (next: list (block T)) : list (block T * ocfg T) :=
    match next with
    | [] => []
    | bk :: next' => match predecessors bk.(blk_id) G with
        | [] => (bk, (remove_blk bk G))::find_heads_rec G next'
        | _ => find_heads_rec G next'
    end end.

Definition find_heads {T} (G: ocfg T) : list (block T * ocfg T) := find_heads_rec G G.

Definition find_seq_proto {T} (G: ocfg T): list (ocfg T * block T * ocfg T) := match G with
    | [] => []
    | B::Q => [([],B,Q)]
end.

Definition Match {T} {S}: Pat T S -> ocfg T -> (S -> bool) -> list S :=
    fun p => fun g => fun b => filter b match p with
        | Head _ => find_heads g
        | Seq _ => find_seq_proto g
end.

Lemma find_heads_rec_cons {T}: forall (L G: ocfg T) (A: block T), find_heads_rec G (A::L) = (find_heads_rec G [A]) ++ (find_heads_rec G L).
Proof.
    cbn. intros. induction (predecessors (blk_id A) G). reflexivity. reflexivity.
Qed.

Lemma find_heads_rec_app {T}: forall (L1 L2 G: ocfg T), find_heads_rec G (L1++L2) = (find_heads_rec G L1) ++ (find_heads_rec G L2).
Proof.
    induction L1 as [|a L1 IHL1]. trivial.
    intros. rewrite <-app_comm_cons. rewrite find_heads_rec_cons.
    replace (find_heads_rec G (a :: L1)) with (find_heads_rec G [a] ++ find_heads_rec G (L1)) by (symmetry; apply find_heads_rec_cons).
    rewrite IHL1. apply app_assoc.
Qed.

Lemma head_rec_correct1 {T}: forall (G L: ocfg T) (B: block T), In B L -> (predecessors B.(blk_id) G = []) -> In (B, remove_blk B G) (find_heads_rec G L).
Proof.
    intros G L B HL Hp. apply in_split in HL. destruct HL as [l1 [l2 HL]].
    subst L. rewrite find_heads_rec_app. apply in_or_app. right.
    simpl. rewrite Hp. left. trivial.
Qed.

Lemma head_rec_correct2_l1 {T}: forall (G L: ocfg T) (B: block T), In (B, remove_blk B G) (find_heads_rec G L) -> In B L.
Proof.
    intro G. induction L as [|a L IHL]. contradiction.
    cbn. intros B Hh. induction (predecessors (blk_id a) G).
    - destruct Hh as [Hh|Hh].
        * left. apply pair_equal_spec in Hh. destruct Hh. trivial.
        * right. apply IHL. trivial.
    - right. apply IHL. trivial.
Qed.

Lemma head_rec_correct2_l2 {T}: forall (G L: ocfg T) (B: block T), In (B, remove_blk B G) (find_heads_rec G L) -> (predecessors B.(blk_id) G = []).
Proof.
    intros G. induction L as [|a L IHL]. contradiction.
    cbn. intros B Hh. assert (Lemme_nul: a=B -> (predecessors (blk_id a) G)=[] -> (predecessors (blk_id B) G) = []). intros. subst a. trivial. induction (predecessors (blk_id a) G).
    - destruct Hh as [Hh|Hh].
        * apply pair_equal_spec in Hh. destruct Hh as [H0 H1]. apply Lemme_nul;trivial.
        * apply IHL. trivial.
    - apply IHL. trivial.
Qed.

Lemma head_rec_correct {T}: forall (G L: ocfg T) (B: block T), In (B, remove_blk B G) (find_heads_rec G L) <-> In B L /\ (predecessors B.(blk_id) G = []).
Proof.
    intros G L. split. split. apply (head_rec_correct2_l1 G). trivial. apply (head_rec_correct2_l2 _ L). trivial. intro H. destruct H. apply head_rec_correct1;trivial.
Qed.

Lemma head_correct {T}: forall (G: ocfg T) (B: block T), In (B, remove_blk B G) (find_heads G) <-> In B G /\ (predecessors B.(blk_id) G = []).
Proof.
    intros. apply head_rec_correct.
Qed.

Theorem pat_head_correct_true {T}: forall (G: ocfg T) (B: block T), In (B, remove_blk B G) (Match (Head T) G (fun x => true)) <-> In B G /\ (predecessors B.(blk_id) G = []) .
Proof.
    intros.
    cbn. rewrite filter_In. split. intro H. destruct H. apply head_correct; trivial. split;trivial. apply head_correct. trivial.
Qed.

Theorem pat_head_correct {T}: forall (G: ocfg T) (B: block T) b, In (B, remove_blk B G) (Match (Head T) G b) -> b (B, remove_blk B G) = true /\ In B G /\ (predecessors B.(blk_id) G = []).
Proof.
    cbn. intros G B b H.
    rewrite filter_In in H. destruct H as [H1 H2].
    split. trivial. apply head_correct; trivial.
Qed.