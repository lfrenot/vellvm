From Vellvm Require Import Syntax ScopeTheory.
Require Import List Lia.
Import ListNotations.

Notation graph := (ocfg dtyp).
Notation blk := (block dtyp).

Inductive Pat : Type -> Type :=
  | Graph: Pat graph
  | When: forall S, Pat S -> (S -> bool) -> Pat S
  | Head: forall S, Pat S -> (S -> graph) -> Pat (blk * graph)
  (* | Seq: forall S, Pat S -> (S -> graph) -> Pat (graph * graph) *)
  | Subgraph: forall S, Pat S -> (S -> graph) -> Pat (graph * graph)
  | Cart: forall S1 S2, Pat S1 -> Pat S2 -> Pat (S1 * S2)
  (* | Loop: Pat T (graph * graph * graph) *)
  .

(* Head Pattern matching *)

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

(* Subgraph Pattern matching *)

Fixpoint subgraph_rec {A} (l1 l2 acc: list A): list (list A*list A) :=
  match acc with
    | [] => [(l1, l2)]
    | a::q => (subgraph_rec (l1++[a]) l2 q) ++ (subgraph_rec l1 (l2++[a]) q)
end.

Definition subgraphs {A} (G: list A) := subgraph_rec [] [] G.

(* Fixpoint subgraph_map_rec {A B} (l1 l2 acc: list A) (f: list A -> list A -> option B): list B :=
  match acc with
    | [] => match f l1 l2 with
      | Some x => [x]
      | _ => []
      end
    | a::q => (subgraph_map_rec (a::l1) l2 q f) ++ (subgraph_map_rec l1 (a::l2) q f)
end. *)

Fixpoint no_intersect l1 l2: bool := match l2 with
  | [] => true
  | a::q => if raw_id_in a l1 then false else no_intersect l1 q
end.

Fixpoint Inn {A} (n: nat) (a:A) (l: list A) : Prop :=
  match l with
  | [] => n=0
  | b::q => match n with
    | 0 => b <> a /\ Inn 0 a q
    | S m => (b=a /\ Inn m a q) \/ (b<>a /\ Inn n a q)
    end
  end.

Definition equiv {A} (l1 l2: list A) := forall (x:A) n, Inn n x l1 <-> Inn n x l2. 

(* Definition find_seqs_aux (G1 G2: graph): option (graph*graph) := if no_intersect (outputs G2) (inputs G1) then Some (G1, G2) else None. *)

(* Fixpoint find_seqs_rec (G: list (graph*graph)): list (graph*graph) := match G with
  | [] => []
  | (G1,G2)::q => if no_intersect (outputs G2) (inputs G1) then (G1,G2)::(find_seqs_rec q) else find_seqs_rec q
end.

Definition find_seqs (G: graph): list (graph*graph) := find_seqs_rec (subgraphs G). *)

(* Pattern matching functions *)

Fixpoint MatchAll {S} (P: Pat S) (G: graph) : list S :=
  match P with
    | When _ p f => filter f (MatchAll p G)
    | Head _ p f => flat_map find_heads (map f (MatchAll p G))
    | Graph => [G]
    | Subgraph _ p f => flat_map subgraphs (map f (MatchAll p G))
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

(* Correction of subgraphs *)

Lemma ABC_ABC: forall A B C, (A \/ B \/ C) <-> ((A\/B) \/ C).
Proof. 
  intros. split; intro H.
  - destruct H as [|[|]]. left. now left. left. now right. now right.
  - destruct H as [[|]|]. now left. right. now left. right. now right.
Qed.

Lemma ABC_ACB: forall A B C, (A \/ B \/ C) <-> ((A \/ C) \/ B).
Proof.
  intros. split; intro H.
  - destruct H as [|[|]]. left. now left. now right. left. now right.
  - destruct H as [[|]|]. now left. right. now right. right. now left.
Qed.

(* Lemma or_in_nil {A}: forall (G: list A) (x:A), (In x [] \/ In x G) -> In x G.
Proof.
  intros G x H. now destruct H.
Qed.

Lemma equiv_incl {A}: forall (l1 l2: list A), equiv l1 l2 <-> (incl l1 l2) /\ (incl l2 l1).
Proof.
  unfold equiv. unfold incl. split; intro H; split;apply H.
Qed.

Lemma in_or_app_single {A}: forall (l: list A) x a, In x (l++[a]) <-> In x l \/ a = x.
Proof.
  intros. split. intro. apply in_app_or in H. cbn in H. destruct H as [|[|]]. now left. now right. contradiction.
  - intro H. apply in_or_app. destruct H as [|]. now left. cbn. right. now left.
Qed. *)

Lemma Inn_app {A}: forall (l1 l2: list A) n m x, Inn n x l1 -> Inn m x l2 -> Inn (n+m) x (l1++l2).
Proof.
  induction l1.
  * cbn. intros. now subst n.
  * induction n. induction m.
    - cbn. intros. destruct H as [H H1]. split; trivial. replace 0 with (0+0) by lia. now apply IHl1.
    - cbn. intros. right. destruct H as [H H1]. split; trivial. replace (S m) with (0 + S m) by lia. now apply IHl1.
    - cbn. intros. destruct H as [[H H1] | [H H1]].
      + left. split; trivial. now apply IHl1.
      + right. split; trivial. replace (S (n+m)) with (S n + m) by lia. now apply IHl1.
Qed.

Lemma subgraph_rec_correct_l: forall (G G1 G2 l1 l2: graph) x n m, In (G1, G2) (subgraph_rec l1 l2 G) -> Inn n x l1 -> Inn m x G -> exists n', n <= n' <= n+m /\ Inn n' x G1.
Proof.
  induction G as [|a G IHG]; intros G1 G2 l1 l2 x n m H H0 H1.
  - exists n. split. lia. destruct H.
    * apply pair_equal_spec in H as []. now subst G1.
    * destruct H.
  - induction m. cbn in H. 1:apply in_app_or in H as [|]; eapply IHG; try apply H; trivial. 4: destruct H1 as [[H1 H2] | [H1 H2]]. 
    * replace n with (n+0) by lia. apply Inn_app. trivial. now destruct H1.
    * now destruct H1.
    * now destruct H1.
    * subst a. cbn in H. apply in_app_or in H as [|]. assert (H': exists n', S n <= n' <= S n + m /\ Inn n' x G1).
      eapply IHG; try apply H; trivial. 3:assert (H': exists n', n <= n' <= n + m /\ Inn n' x G1). 3:eapply IHG; try apply H; trivial.
      + replace (S n) with (n + 1) by lia. apply Inn_app. trivial. now left.
      + destruct H' as [n' [H' H'']]. exists n'. split. lia. trivial.
      + destruct H' as [n' [H' H'']]. exists n'. split. lia. trivial.
    * cbn in H. apply in_app_or in H as [|]; eapply IHG; try apply H; trivial.
      replace n with (n+0) by lia. now apply Inn_app.
Qed.

Lemma subgraph_rec_correct_r: forall (G G1 G2 l1 l2: graph) x n m, In (G1, G2) (subgraph_rec l1 l2 G) -> Inn n x l2 -> Inn m x G -> exists n', n <= n' <= n+m /\ Inn n' x G2.
Proof.
  induction G as [|a G IHG]; intros G1 G2 l1 l2 x n m H H0 H1.
  - exists n. split. lia. destruct H.
    * apply pair_equal_spec in H as []. now subst G2.
    * destruct H.
  - induction m. cbn in H. 1:apply in_app_or in H as [|]; eapply IHG; try apply H; trivial. 4: destruct H1 as [[H1 H2] | [H1 H2]].
    * now destruct H1.
    * replace n with (n+0) by lia. apply Inn_app. trivial. now destruct H1.
    * now destruct H1.
    * subst a. cbn in H. apply in_app_or in H as [|]. assert (H': exists n', n <= n' <= n + m /\ Inn n' x G2). eapply IHG; try apply H; trivial.
      2: assert (H': exists n', S n <= n' <= S n + m /\ Inn n' x G2). 2: eapply IHG; try apply H; trivial.
      + destruct H' as [n' [H' H'']]. exists n'. split. lia. trivial.
      + replace (S n) with (n + 1) by lia. apply Inn_app. trivial. now left.
      + destruct H' as [n' [H' H'']]. exists n'. split. lia. trivial.
    * cbn in H. apply in_app_or in H as [|]; eapply IHG; try apply H; trivial.
      replace n with (n+0) by lia. now apply Inn_app.
Qed.

(* Lemma subgraph_rec_correct_g: forall (G G1 G2 l1 l2: graph), In (G1, G2) (subgraph_rec l1 l2 G) -> equiv (G1++G2) (G++l1++l2).
Proof.
  induction G as [|a G IHG];cbn;intros G1 G2 l1 l2 H x n.
  - destruct H; try contradiction. apply pair_equal_spec in H as []. now subst l1 l2.
  - rewrite Util.list_cons_app. replace ([a] ++ G ++ l1 ++ l2) with (G++(l1++[a])++l2) by admit. apply IHG.
Abort. *)

(* Lemma subgraph_rec_correct1_l: forall (G G1 G2 l1 l2: graph) x n m, In (G1, G2) (subgraph_rec l1 l2 G) -> Inn n x G1 -> Inn m x l1 -> exists n', n <= n' <= n+m /\ Inn n' x G. *)

(* Lemma subgraph_rec_correct1_l: forall (G G1 G2 l1 l2: graph) x n m, In (G1, G2) (subgraph_rec l1 l2 G) -> Inn n x G1 -> In x l1 \/ In x G.
Proof.
  induction G as [|a G IHG];cbn;intros G1 G2 l1 l2 x H H0. destruct H. 3:apply in_app_or in H as [|].
  - apply pair_equal_spec in H as [H1 H2]. subst G1. now left.
  - contradiction.
  - apply ABC_ABC. rewrite <-in_or_app_single. eapply IHG. apply H. apply H0.
  - apply ABC_ACB. left. eapply IHG. apply H. trivial.
Qed.

Lemma subgraph_rec_correct1_r: forall (G G1 G2 l1 l2: graph) x, In (G1, G2) (subgraph_rec l1 l2 G) -> In x G2 -> In x l2 \/ In x G.
Proof.
  induction G as [|a G IHG];cbn;intros G1 G2 l1 l2 x H H0. destruct H. 3:apply in_app_or in H as [|].
  - apply pair_equal_spec in H as [H1 H2]. subst G2. now left.
  - contradiction.
  - apply ABC_ACB. left. eapply IHG. apply H. trivial.
  - apply ABC_ABC. rewrite <-in_or_app_single. eapply IHG. apply H. apply H0.
Qed. *)


(* Lemma subgraphs_correct1: forall (G G1 G2: graph), In (G1,G2) (subgraphs G) -> equiv G (G1++G2).
Proof.
  intro G. induction G; intros G1 G2 H;split. intro. destruct H as [|].
  - apply pair_equal_spec in H as []. now subst G1 G2.
  - contradiction.
  - intro H0; destruct H0; apply in_or_app. subst a. apply in_app_or in H as [|].
    * left. eapply subgraph_rec_correct_l. apply H. now left.
    * right. eapply subgraph_rec_correct_r. apply H. now left.
    * apply in_app_or in H as [|];eapply subgraph_rec_correct_g. apply H. trivial. apply H. trivial.
  - intro H0; apply in_app_or in H0 as [];apply or_in_nil.
    * eapply subgraph_rec_correct1_l. apply H. trivial.
    * eapply subgraph_rec_correct1_r. apply H. trivial.
Abort.

Lemma subgraph_correct2: forall (G G1 G2: graph), equiv G (G1++G2) -> (exists G1' G2', In (G1', G2') (subgraphs G) /\ equiv G1 G1' /\ equiv G2 G2').
Proof.
  induction G as [|a G IHG].
  - intros. exists [], []. unfold equiv in H. split. 2: split;split.
    * cbn. now left.
    * intro. apply H. apply in_or_app. now left.
    * now cbn.
    * intro. apply H. apply in_or_app. now right.
    * now cbn.
  - intros. eexists. eexists. split. 2:split.
    * cbn. apply in_or_app.
Abort.


Lemma subgraphs_correct2: forall (G' G: graph), incl G' G -> exists G1 G2, equiv G1 G' /\ In (G1, G2) (subgraphs G).
Proof.
  intro G'. induction G'.
  - cbn. intros. exists [], (rev G). split. now cbn. induction G. cbn. now left. 
Abort.

Lemma subgraphs_correct2: forall (G G1 G2: graph) x, In x G -> In (G1,G2) (subgraphs G) -> (In x G1 \/ In x G2).
Proof.
  intro G. induction G;cbn;intros G1 G2 x H H0.
  - contradiction.
  -  
Abort. *)

(* Correction of no_intersect *)

Lemma inputs_cons: forall (G: graph) a, inputs (a::G) = (blk_id a) :: (inputs G). Proof. now cbn. Qed.

Lemma list_disjoint_cons_r_iff:
    forall (A: Type) (a: A) (l1 l2: list A),
    Coqlib.list_disjoint (l1) (a :: l2) <->
    (Coqlib.list_disjoint l1 l2 /\ not (In a l1)).
  Proof.
    split; intros H.
    - split; [eapply Coqlib.list_disjoint_cons_right; eauto |].
      intros abs; eapply H; eauto; constructor; reflexivity.
    - apply Coqlib.list_disjoint_cons_r; apply H. 
Qed.

Lemma no_intersect_correct: forall (G1 G2: graph), no_intersect (outputs G2) (inputs G1) = true <-> no_reentrance G1 G2.
Proof.
  intros G1 G2. induction G1 as [|a G1 IHG1];split; intro H.
  - now apply Util.list_disjoint_nil_r.
  - now trivial.
  - inversion H. unfold no_reentrance. rewrite inputs_cons. apply Coqlib.list_disjoint_cons_r.
    * replace (Coqlib.list_disjoint (outputs G2) (inputs G1)) with (no_reentrance G1 G2) by (trivial).
      apply IHG1. induction (no_intersect (outputs G2) (inputs G1)).
      trivial. now induction (raw_id_in (blk_id a) (outputs G2)).
    * now induction (raw_id_in (blk_id a) (outputs G2)).
  - assert (H0: no_intersect (outputs G2) (inputs (a :: G1)) = true).
    * rewrite inputs_cons. cbn. induction (raw_id_in (blk_id a) (outputs G2)).
      + unfold no_reentrance in H. rewrite inputs_cons in H. now apply list_disjoint_cons_r_iff in H as [].
      + unfold no_reentrance in H. rewrite inputs_cons in H. apply list_disjoint_cons_r_iff in H as [].
        unfold no_reentrance in IHG1. now apply IHG1.
    * now induction (no_intersect (outputs G2) (inputs (a :: G1))).
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

Theorem pat_subgraph_correct {S}: forall (P: Pat S) f G G1 G2, In (G1, G2) (MatchAll (Subgraph _ P f) G) <-> exists G' G1' G2', equiv G1 G1' /\ equiv G2 G2' /\ In G' (map f (MatchAll P G)) /\ equiv G' (G1'++G2').
Proof.
Abort.