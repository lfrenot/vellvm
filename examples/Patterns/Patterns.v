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
Proof.
  intros b g Hwf id a H. 
  apply MapF.P.F.remove_mapsto_iff in H as [ ]. now apply Hwf.
Qed.

(* Pattern definition *)

Inductive Pat : Type -> Type :=
  | Graph: Pat mcfg
  | When: forall S, Pat S -> (S -> bool) -> Pat S
  | Head: forall S, Pat S -> Pat (blk * S)
  | Focus: forall S, Pat S -> Pat (mcfg * S)
  | Map: forall S T, Pat S -> (S -> T) -> Pat T
  .

(* Head Definitions *)

Definition predecessors_aux (b id: bid) (bk: blk) acc := if is_predecessor b bk then Map.add id bk acc else acc.

Definition predecessors (b : bid) (G : mcfg) : mcfg :=
    Map.fold (predecessors_aux b) G (Map.empty blk).

Definition find_heads_aux (G: mcfg) id b acc : list (blk*mcfg) :=
  if Map.is_empty (predecessors id G)
  then (b, Map.remove id G)::acc
  else acc.

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

Definition is_head (G G':mcfg) (b:blk) :=
  Map.Equal (Map.remove b.(blk_id) G) G' /\ wf_mcfg G' /\
  Map.MapsTo b.(blk_id) b G /\ Map.Empty (predecessors b.(blk_id) G).

Lemma head_correct: forall G G' b, wf_mcfg G -> (In (b, G') (find_heads G) <-> is_head G G' b).
Admitted.

(* Correction of focus *)

Definition is_focus (G G1 G2: mcfg) := MapF.P.Partition G G1 G2 /\ wf_mcfg G1 /\ wf_mcfg G2.

Lemma focus_correct: forall G G1 G2, wf_mcfg G -> (In (G1, G2) (focus G)) <-> is_focus G G1 G2.
Admitted.

(* Correction de MatchAll *)

Theorem pat_graph_correct: forall G G', In G' (MatchAll Graph G) -> G' = G. Proof.
  cbn. intros G G' H. destruct H; now destruct H.
Qed.

Lemma map_empty_mapsto: forall (G:mcfg) id b, Map.Empty G -> ~Map.MapsTo id b G.
Proof.
  intros G id b H H0. eapply InA_nil. apply MapF.P.elements_Empty in H.
  rewrite <-H. apply Map.elements_1. apply H0.
Qed.

Lemma in_flat_map_r {A B C}:
  forall (f:B->list C) (l:list (A*B)) (a:A) (c:C), In (a,c) (flat_map_r f l) <->
  exists b, In (a,b) l /\ In c (f b).
Proof.
  intro f. induction l as [|[a b] l IHl].
  * intros. split. contradiction. intros [b [H1 H2]]. contradiction.
  * intros a' c'. split.
    - cbn. intro H. apply in_app_or in H as [].
      + exists b.
        apply Coqlib.list_in_map_inv in H as [c'' [H1 H2]]. apply pair_equal_spec in H1 as [].
        subst a' c''.
        split; trivial. left. apply pair_equal_spec. now split.
      + assert (H': exists b0 : B, In (a', b0) l /\ In c' (f b0)) by now apply IHl.
        destruct H' as [b' [H1 H2]]. exists b'. split; trivial. now right.
    - intros [b' [[H1|H1] H2]];cbn; apply in_or_app.
      + apply pair_equal_spec in H1 as []. subst a' b'. left. now apply in_map.
      + right. apply IHl. now exists b'. 
Qed.

Theorem pat_head_correct {S}:
  forall (G: mcfg)(P: Pat S) (b:blk) s, wf_mcfg G ->
  In (b, s) (MatchAll (Head _ P) G) <-> exists G', is_head G G' b /\ In s (MatchAll P G').
Proof.
  intros G P b s Hwf. setoid_rewrite <-head_correct;trivial. apply in_flat_map_r.
Qed.

Theorem pat_focus_correct {S}:
  forall (G G1: mcfg) (P:Pat S) s, wf_mcfg G ->
  In (G1, s) (MatchAll (Focus _ P) G) <-> exists G2, is_focus G G1 G2 /\ In s (MatchAll P G2).
Proof.
  intros G G1 P s Hwf. setoid_rewrite <-focus_correct;trivial. apply in_flat_map_r.
Qed.

Theorem pat_when_correct {S}:
  forall (P: Pat S) f x G,
  In x (MatchAll (When _ P f) G) <-> In x (MatchAll P G) /\ f x = true.
Proof.
  intros. apply filter_In.
Qed.

Theorem pat_map_correct {S T}:
  forall (P: Pat S) (f: S -> T) x G,
  In x (MatchAll (Map _ _ P f) G) <-> exists y, f y = x /\ In y (MatchAll P G).
Proof.
  cbn. intros P f x G. split.
  - intro H. apply Coqlib.list_in_map_inv in H as [y [H1 H2]]. now exists y.
  - intros [y [H1 H2]]. subst x. now apply in_map.
Qed.

(* Block Fusion Pattern *)

Definition is_seq (X: blk*(blk*mcfg)) := match X with |(A,(B,G)) => match successors A with
    | [x] =>  if IdOT.eq_dec x B.(blk_id)
              then Map.is_empty (predecessors B.(blk_id) G)
              else false
    | _ => false
  end
end.

Definition DoubleHead := When _ (Head _ (Head _ Graph)) (fun x => is_seq x).

Definition BlockFusion_aux (x: (mcfg*(blk*(blk*mcfg)))) :=
  match x with | (G,(_,(B,_))) => Map.is_empty (predecessors B.(blk_id) G) end.

Definition BlockFusion := When _ (Focus _ DoubleHead) (fun x => BlockFusion_aux x).

Lemma is_seq_correct:
  forall A B G, is_seq (A ,(B ,G)) = true ->
  successors A = [B.(blk_id)] /\ Map.Empty (predecessors B.(blk_id) G).
Proof.
  unfold is_seq. intros A B G H.
  induction (successors A) as [|a l IHl]; try discriminate;
  induction l, (IdOT.eq_dec a (blk_id B)) as [He|He]; try discriminate.
  apply IdOT.eq_eq in He. subst a. split; trivial.
  now apply Map.is_empty_2.
Qed.

Lemma add_remove_elim1:
  forall id B (G: mcfg), Map.MapsTo id B G -> Map.Equal (Map.add id B (Map.remove id G)) G.
Proof.
  intros id B G H. apply MapF.P.F.Equal_mapsto_iff.
  intros k e. split; intro H'.
  - apply MapF.P.F.add_mapsto_iff in H' as [[He H']| [Hne H']].
    * apply IdOT.eq_eq in He. now subst e k.
    * eapply Map.remove_3. apply H'.
  - induction (IdOT.eq_dec id k) as [He|He].
    * assert (He': B=e). eapply MapF.P.F.MapsTo_fun.
      apply H. eapply Map.MapsTo_1. apply IdOT.eq_sym in He. apply He. trivial.
      subst e. now apply Map.add_1.
    * apply Map.add_2; trivial. now apply Map.remove_2.
Qed.

Lemma add_remove_elim2:
  forall id B (G G': mcfg), Map.MapsTo id B G ->
  Map.Equal (Map.remove id G) G' -> Map.Equal (Map.add id B G') G.
Proof.
  intros id B G G' Hm He.
  eapply MapF.P.F.Equal_trans. 2: apply add_remove_elim1.
  apply MapF.P.F.add_m. apply IdOT.eq_refl. reflexivity.
  now apply MapF.P.F.Equal_sym. trivial.
Qed.

Lemma Proper_predecessor_aux: forall id, Proper (IdOT.eq ==> eq ==> Map.Equal ==> Map.Equal) (predecessors_aux id).
Proof.
  intros id idB idB' H B B' H0 x1 y1 H1 y2. subst B'. apply IdOT.eq_eq in H. subst idB'.
  unfold predecessors_aux. remember (is_predecessor id B) as b. induction b.
  - apply MapF.P.F.find_m_Proper. apply IdOT.eq_refl. apply MapF.P.F.add_m_Proper; trivial. apply IdOT.eq_refl.
  - apply MapF.P.F.find_m_Proper; trivial. apply IdOT.eq_refl.
Qed.

Lemma swap_add:
  forall id id' B B' (G : mcfg), ~ IdOT.eq id id' ->
  Map.Equal (Map.add id B (Map.add id' B' G)) (Map.add id' B' (Map.add id B G)).
Proof.
  intros id id' B B' G Hn.
  apply MapF.P.F.Equal_mapsto_iff. intros k e. induction (IdOT.eq_dec k id) as [b|b]. 2: induction (IdOT.eq_dec k id') as [b'|b'].
  - apply IdOT.eq_eq in b. subst k.
    split; intro H. assert (He: B=e).
    apply MapF.P.F.add_mapsto_iff in H as [[H1 H2]|[H1 H2]]. trivial. contradict H1. apply IdOT.eq_refl. subst e.
    apply Map.add_2.
      * now apply IdOT.neq_sym. 
      * apply MapF.P.F.add_mapsto_iff. left.
        apply MapF.P.F.add_mapsto_iff in H as [|[H1 H2]]. trivial. contradict H1. apply IdOT.eq_refl.
      * assert (He: B=e).
        apply Map.add_3 in H. apply MapF.P.F.add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
        trivial. contradict H1. apply IdOT.eq_refl.
        now apply IdOT.neq_sym.
        subst e.
        apply Map.add_1. apply IdOT.eq_refl.
  - apply IdOT.eq_eq in b'. subst k.
    split; intro H.
    * assert (He: B'=e).
      apply Map.add_3 in H. apply MapF.P.F.add_mapsto_iff in H as [[H1 H2]|[H1 H2]].
      trivial. contradict H1. apply IdOT.eq_refl. trivial.
      subst e.
      apply Map.add_1. apply IdOT.eq_refl.
    * assert (He: B'=e). apply MapF.P.F.add_mapsto_iff in H as [[H1 H2]|[H1 H2]]. trivial. contradict H1. apply IdOT.eq_refl. subst e.
      apply Map.add_2. trivial. apply Map.add_1. apply IdOT.eq_refl.
  - split; intro H.
    * assert (H': Map.MapsTo k e G).
      eapply Map.add_3. apply IdOT.neq_sym. apply b'.
      eapply Map.add_3. apply IdOT.neq_sym. apply b. apply H.
      apply Map.add_2. now apply IdOT.neq_sym. apply Map.add_2. now apply IdOT.neq_sym. trivial.
    * assert (H': Map.MapsTo k e G).
      eapply Map.add_3. apply IdOT.neq_sym. apply b.
      eapply Map.add_3. apply IdOT.neq_sym. apply b'. apply H.
      apply Map.add_2. now apply IdOT.neq_sym. apply Map.add_2. now apply IdOT.neq_sym. trivial.
Qed.

Lemma transpose_neqkey_predecessor_aux: forall id, MapF.P.transpose_neqkey Map.Equal (predecessors_aux id).
Proof.
  intros id idB idB' B B' G H id'. assert (Hn: ~IdOT.eq idB idB') by apply H. clear H.
  unfold predecessors_aux. remember (is_predecessor id B) as b. remember (is_predecessor id B') as b'.
  induction b, b'; trivial.
  apply MapF.P.F.find_m_Proper. apply IdOT.eq_refl. apply swap_add. apply Hn.
Qed.

Lemma Eempty_Map: forall (G: mcfg), Map.Empty G <-> Map.Equal G (Map.empty _).
Proof.
  apply MapF.P.map_induction_bis.
  - intros. split; intro H'.
    eapply MapF.P.F.Equal_trans. apply MapF.P.F.Equal_sym. apply H. apply H0.
    eapply MapF.P.F.Empty_m. apply H. trivial.
    eapply MapF.P.F.Empty_m. apply MapF.P.F.Equal_sym. apply H. apply H0.
    eapply MapF.P.F.Equal_trans. apply H. trivial.
  - split; intro. apply MapF.P.F.Equal_refl. apply Map.empty_1.
  - split; intro H'.
    * assert (H1: Map.MapsTo x e (Map.add x e m)).
      apply MapF.P.F.add_mapsto_iff. left. split; trivial. apply IdOT.eq_refl.
      contradict H1. now apply map_empty_mapsto.
    * assert (H1: Map.MapsTo x e (Map.add x e m)).
      apply MapF.P.F.add_mapsto_iff. left. split; trivial. apply IdOT.eq_refl.
      contradict H'.
      intro. eapply MapF.P.F.empty_mapsto_iff.
      eapply MapF.P.F.Equal_mapsto_iff. apply MapF.P.F.Equal_sym. apply H2.
      apply H1.
Qed.

Lemma add_predecessor: forall (A B: blk) G, wf_mcfg G -> Map.MapsTo (blk_id A) A G ->
  Map.Empty (predecessors B.(blk_id) (Map.remove A.(blk_id) G)) -> successors A = [B.(blk_id)] ->
  Map.Equal (predecessors B.(blk_id) G) (Map.add A.(blk_id) A (Map.empty _)).
Proof.
  intros. remember (Map.remove (elt:=blk) (blk_id A) G) as G'.
  assert (H': Map.Equal (Map.add A.(blk_id) A G') G).
  {
    apply add_remove_elim2. trivial. rewrite HeqG'. apply MapF.P.F.Equal_refl.
  }
  unfold predecessors. erewrite MapF.P.fold_Equal. 5: apply MapF.P.F.Equal_sym in H'; apply H'.
  {
    eapply MapF.P.F.Equal_trans.
      - assert (H3: Map.Equal
                (Map.fold (predecessors_aux (blk_id B)) (Map.add (blk_id A) A G') (Map.empty blk))
                (predecessors_aux (blk_id B) (blk_id A) A (Map.fold (predecessors_aux (blk_id B)) G' (Map.empty blk)))).
      {
        apply MapF.P.fold_add. auto. apply Proper_predecessor_aux. apply transpose_neqkey_predecessor_aux.
        rewrite HeqG'. apply Map.remove_1. apply IdOT.eq_refl.
      }
      apply H3.
    - eapply MapF.P.F.Equal_trans.
      * apply Proper_predecessor_aux. apply IdOT.eq_refl. reflexivity. apply Eempty_Map. apply H1.
      * unfold predecessors_aux. unfold is_predecessor. rewrite H2. cbn.
        induction (raw_id_eq_dec (blk_id B) (blk_id B)). apply MapF.P.F.Equal_refl. contradiction.
  }
  auto. apply Proper_predecessor_aux. apply transpose_neqkey_predecessor_aux.
Qed.

Theorem DoubleHead_correct: forall A B G' G,
  wf_mcfg G -> In (A,(B,G')) (MatchAll DoubleHead G) ->
  successors A = [B.(blk_id)] /\ Map.Equal (predecessors B.(blk_id) G) (Map.add A.(blk_id) A (Map.empty _)) /\
  Map.Equal (Map.add A.(blk_id) A (Map.add B.(blk_id) B G')) G /\ wf_mcfg G'.
Proof.
  unfold DoubleHead.
  intros A B G' G Hwf H.
  apply pat_when_correct in H as [H HWhen].
  apply pat_head_correct in H as [G2 [[HRA [HwfA [HMA HPA]]] H]]; trivial.
  apply pat_head_correct in H as [G3 [[HRB [HwfB [HMB HPB]]] H]]; trivial.
  apply pat_graph_correct in H. destruct H.
  apply is_seq_correct in HWhen as [Hsucc HPrec].
  repeat split; trivial.
  - apply add_predecessor; trivial. eapply MapF.P.F.Empty_m. unfold predecessors. eapply MapF.P.fold_Equal.
    * auto.
    * apply Proper_predecessor_aux.
    * apply transpose_neqkey_predecessor_aux.
    * apply HRA.
    * trivial.    
  - apply add_remove_elim2. trivial.
    eapply MapF.P.F.Equal_trans.
    apply HRA.
    apply MapF.P.F.Equal_sym.
    now apply add_remove_elim2.
Qed.

Theorem BlockFusion_correct: forall A B G G' G'',
  wf_mcfg G -> In (G'', (A, (B, G'))) (MatchAll BlockFusion G) ->
  successors A = [B.(blk_id)] /\ Map.Equal (predecessors B.(blk_id) G) (Map.add A.(blk_id) A (Map.empty _)) /\
  MapF.P.Partition G G'' (Map.add A.(blk_id) A (Map.add B.(blk_id) B G')) /\
  wf_mcfg G'' /\ wf_mcfg G'.
Proof.
  unfold BlockFusion.
  intros A B G G' G'' Hwf H.
  apply pat_when_correct in H as [H HWhen]. unfold BlockFusion_aux in HWhen.
  apply pat_focus_correct in H as [G0 [[HPart [Hwf'' Hwf0]] H]]; trivial.
  apply DoubleHead_correct in H as [HS [HP [HG' Hwf']]]; trivial.
  split; trivial. split. 2:split. 3:split; trivial.
  - eapply MapF.P.F.Equal_trans.
    assert (Map.Equal (Map.fold (predecessors_aux (blk_id B)) G (Map.empty blk)) (Map.fold (predecessors_aux (blk_id B)) G0 (Map.fold (predecessors_aux (blk_id B)) G'' (Map.empty blk)) )).
    eapply MapF.P.Partition_fold.
    * auto.
    * apply Proper_predecessor_aux.
    * apply transpose_neqkey_predecessor_aux.
    * now apply MapF.P.Partition_sym.
    * apply H.
    * eapply MapF.P.F.Equal_trans. eapply MapF.P.fold_Equal2. auto. apply Proper_predecessor_aux.
      apply transpose_neqkey_predecessor_aux. apply MapF.P.F.Equal_refl. apply Eempty_Map. now apply Map.is_empty_2.
      trivial.
  - eapply MapF.P.Partition_m.
    * apply MapF.P.F.Equal_refl.
    * apply MapF.P.F.Equal_refl.
    * apply HG'.
    * trivial.
Qed.