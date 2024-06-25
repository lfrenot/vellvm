(** This file contains the proof of correctness of the Conditional Constant Propagation optimization.
    It relies on the garantees given by the [BlockFusion] pattern and on proofs form the [Denotation] file. *)

From Vellvm Require Import Syntax ScopeTheory Semantics Theory Tactics Denotation DenotationTheory.
From ITree Require Import ITree Eq HeterogeneousRelations.
From Pattern Require Import Base Patterns Denotation BlockFusion.
From Paco Require Import paco.
From stdpp Require Import prelude fin_maps strings.
Import List Head Focus Block Patterns gmap Utils.Monads PostConditions Pattern.Denotation.

(** [promote_phis] doesn't work at this level because of the interpretation differences between simultaneous phi-nodes and affectation instructions.
    It is kept to simplify the proof strucutre. *)

Definition promote_phi (idA : block_id) (Φ : local_id * phi dtyp) : option (instr_id * instr dtyp) :=
  match Φ with
  | (x, (Phi _ args)) =>
      match args !! idA with
      | None => None
      | Some e => Some (IId x, INSTR_Op e)
      end end.

Definition promote_phis (idA : block_id) (Φs : list (local_id * phi dtyp)) : code dtyp :=
  fold_left
    (fun acc φ => match promote_phi idA φ with
               | None => acc
               | Some i => acc ++ [i]
               end)
    Φs [].

Definition fusion_code (idA : block_id) (A B: blk): code dtyp :=
  A.(blk_code) ++ promote_phis idA B.(blk_phis) ++ B.(blk_code).

Definition fusion_comments (A B: blk) :=
  match (A.(blk_comments), B.(blk_comments)) with
    | (Some cA, Some cB) => Some (cA++cB)
    | (Some cA, _) => Some cA
    | (_, Some cB) => Some cB
    | (_, _) => None
  end.

Definition fusion (σ: bid_renaming) (idA : block_id) (A B: blk): blk := {|
  blk_phis       := A.(blk_phis);
  blk_code       := fusion_code idA A B;
  blk_term       := term_rename σ B.(blk_term);
  blk_comments   := fusion_comments A B
|}.

Definition σfusion idA idB := fun (id: bid) => if decide (id=idA) then idB else id.

Module Type Theory (LP : LLVMParams.LLVMParams).
Module DE := Denotation.Make LP.
Import DE.
Import DT.
Import DT.D.
Import LP.
Import SemNotations.
Import MonadNotation.
Import Events.DV.

Variant hidden_cfg  (T: Type) : Type := boxh_cfg (t: T).
Variant visible_cfg (T: Type) : Type := boxv_cfg (t: T).
Ltac hide_cfg :=
  match goal with
  | h : visible_cfg _ |- _ =>
      let EQ := fresh "VG" in
      destruct h as [EQ];
      apply boxh_cfg in EQ
  | |- context[denote_ocfg ?cfg _] =>
      remember cfg as G eqn:VG;
      apply boxh_cfg in VG
  end.
Ltac show_cfg :=
  match goal with
  | h: hidden_cfg _ |- _ =>
      let EQ := fresh "HG" in
      destruct h as [EQ];
      apply boxv_cfg in EQ
  end.
Notation "'hidden' G" := (hidden_cfg (G = _)) (only printing, at level 10).


Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
        (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
        ).
End eutt_Notations.
Import eutt_Notations.

Lemma fusion_correct {S} G idA A idB B P (X:S):
  let σ := σfusion idA idB in
  (idA, A, (idB, B, X)) ∈ (MatchAll (BlockFusion P) G) ->
  denote_ocfg_equiv_cond {[idA := A; idB := B]} {[idB := fusion σ idA A B]} {[idB]} σ.
Proof.
  intros σ IN. apply Pattern_BlockFusion_correct in IN as (G' & _ & FUS); auto.
  destruct FUS as [EQ NEQAB LUA LUB PRED SUCC PHI].
  unfold denote_ocfg_equiv_cond.
  einit.
  ecofix cih.
  clear cihH.
  intros * NINh.
  apply not_elem_of_singleton in NINh.
  case (decide (header = idA)) as [->|NEQ].

  - subst σ. unfold σfusion.
    case_match; try done.
    simplify_eq.
    rewrite ?denote_ocfg_in_eq_itree; try by simplify_map_eq.
    destruct A as [phisA codeA termA cA].
    remember {| blk_phis := phisA; blk_code := codeA; blk_term := termA; blk_comments := cA |} as A.
    Arguments denote_code : simpl never.
    Arguments denote_phis : simpl never.
    Arguments promote_phis : simpl never.
    Opaque denote_phis.
    Opaque denote_code.

    cbn. unfold fusion_code.
    setoid_rewrite bind_bind.
    ebind. econstructor; [reflexivity|]. intros [] ? <-.
    setoid_rewrite bind_bind.
    rewrite denote_code_app_eq_itree.
    setoid_rewrite bind_bind.
    ebind. econstructor; [reflexivity|]. intros [] ? <-.
    cbn in SUCC. rewrite SUCC. cbn. rewrite bind_ret_l.
    rewrite tau_euttge.
    rewrite ?denote_ocfg_in_eq_itree; try by simplify_map_eq.
    destruct B as [phisB codeB termB cB].
    remember {| blk_phis := phisB; blk_code := codeB; blk_term := termB; blk_comments := cB |} as B.
    cbn in *.
    setoid_rewrite bind_bind.
    rewrite denote_code_app_eq_itree.
    setoid_rewrite bind_bind.
    ebind. econstructor.
    rewrite !PHI. unfold promote_phis. cbn. rewrite denote_phis_nil. rewrite denote_code_nil. reflexivity.
    intros [] ? <-.
    ebind. econstructor. reflexivity. intros [] ? <-.
    ebind. econstructor. eapply has_post_enrich_eutt; [ | | apply term_rename_eutt].
    apply denote_terminator_exits_in_outputs.
    apply denote_terminator_exits_in_outputs.
    intros [] [] (REL1 & REL2 & REL3); inversion REL3.
    * etau. rewrite <- H2. ebase. right. apply cihL.
      apply not_elem_of_singleton. intro EQb. 
      subst b a1 a2. case_match. now subst. subst b0.
      assert (BIN: idB ∈ successors B). {
        inversion REL1. unfold successors. apply H2.
      }
      pose proof predecessors_elem_of G _ LUB BIN.
      rewrite PRED in H1. set_solver.
    * eret. now subst.

  - assert (EQσ: σ header = header). {
      subst σ. unfold σfusion. case_match. now subst. reflexivity.
    } rewrite EQσ.
    rewrite denote_ocfg_nin_eq_itree; [|now simplify_map_eq].
    rewrite denote_ocfg_nin_eq_itree; [|now simplify_map_eq].
    eret.
Qed.

Theorem Denotation_BlockFusion_correct {S} G idA A idB B f to P (X:S):
  let σ := σfusion idA idB in
  let G0 := delete idB (delete idA G) in
  to <> idB ->
  (idA, A, (idB, B, X)) ∈ (MatchAll (BlockFusion P) G) ->
  ⟦ G ⟧bs (f, to) ≈ ⟦ <[idB:=fusion σ idA A B]> (ocfg_term_rename σ G0) ⟧bs (f, σ to).
Proof.
  intros * ineq1 IN.
  apply Pattern_BlockFusion_correct in IN as (G' & INX & FUS); auto.
  destruct FUS as [EQ LUA LUB PRED SUCC].
  assert (G0 = G') as -> by now subst G0 G'.
  assert (BNIN: idB ∉ outputs G'). {
    unfold outputs. intros H. apply elem_of_fold_bk_acc in H as (id & bk & H1 & H2).
    unfold outputs_acc in H2. simplify_map_eq.
    apply lookup_delete_Some in H1 as [? H1]. apply lookup_delete_Some in H1 as [? H1]. 
    pose proof predecessors_elem_of G _ H1 H2 as H3. apply H0.
    rewrite SUCC in H3. now apply elem_of_singleton in H3.
  }
  assert (EQG: G = {[idA:=A;idB:=B]} ∪ G'). {
    assert (H: {[idA:=A;idB:=B]} ∪ G' = <[idA:=A]> (<[idB:=B]> G')). {
      rewrite ?insert_union_singleton_l. symmetry. apply map_union_assoc.
    }
    rewrite H.
    simplify_map_eq. rewrite ?insert_delete; simplify_map_eq; trivial.
  }
  rewrite insert_union_singleton_l, EQG. clear EQG.
  apply denote_ocfg_equiv with (nTO:={[idB]}); auto; unfold inputs in *.
    * rewrite dom_insert_L, !dom_singleton_L.
      replace ({[idB]} ∖ {[idA; idB]}) with (∅: gset bid) by set_solver.
      apply empty_subseteq.
    * rewrite dom_insert_L, !dom_singleton_L. apply elem_of_subseteq_singleton. set_solver.
    * now apply disjoint_singleton_l.
    * apply map_disjoint_insert_r. split. now simplify_map_eq.
      apply map_disjoint_singleton_r. now simplify_map_eq.
    * apply map_disjoint_singleton_r. apply find_block_none_ocfg_term_rename. now simplify_map_eq.
    * split; intros id H.
      + unfold inputs in *. rewrite dom_insert_L in H. rewrite dom_singleton_L in H |- *.
        subst σ. unfold σfusion. case_match; set_solver.
      + subst σ. unfold σfusion. assert (id ≠ idA) by now (intros ->; set_solver). now case_match.
    * eapply fusion_correct. apply Pattern_BlockFusion_correct. exists G'. split; cycle 1.
      split. apply EQ. all:trivial. apply INX.
    * now apply not_elem_of_singleton.
Qed.

End Theory.