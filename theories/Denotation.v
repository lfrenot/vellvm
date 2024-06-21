(** This file contains the tools to prove the correctness of optimizations. *)

From Vellvm Require Import Syntax ScopeTheory Semantics Theory Tactics Denotation DenotationTheory.
From ITree Require Import ITree Eq HeterogeneousRelations.
From Pattern Require Import Base Patterns BlockFusion CCstP.
From Paco Require Import paco.
From stdpp Require Import prelude fin_maps strings.
Import List Head Focus Block Patterns gmap Utils.Monads PostConditions.

(* BEGIN TO MOVE *)
Lemma raise_raise_eutt : forall {E A} Q `{FailureE -< E} s,
    eutt Q (@raise E A _ s) (@raise E A _ s).
Proof.
  intros.
  ibind=; intros [].
Qed.

Lemma raise_raiseUB_eutt : forall {E A} Q `{UBE -< E} s,
    eutt Q (@raiseUB E _ A s) (@raiseUB E _ A s).
Proof.
  intros.
  ibind=; intros [].
Qed.

Lemma map_monad_itree_Forall2 :
  forall {A B E} (l l' : list A) (f f' : A -> itree E B) (P : B -> B -> Prop),
    Forall2 (fun x y => eutt P (f x) (f' y)) l l' ->
    eutt (Forall2 P) (map_monad f l) (map_monad f' l').
Proof.
  intros * HIND.
  revert l' HIND.
  induction l as [| a l IH]; intros l' HIND.
  - apply Forall2_nil_inv_l in HIND; subst.
    by apply eutt_Ret.
  - apply Forall2_cons_inv_l in HIND as (y & l'' & Pf & HIND & ->).
    ibind;[apply Pf |].
    intros * HP.
    ibind; [by apply IH |].
    intros ?? HFORALL; apply eutt_Ret.
    by apply Forall2_cons.
Qed.

Lemma has_post_enrich_eutt {E R S Qt Qu RR} (t : itree E R) (u : itree E S):
  t ⤳ Qt ->
  u ⤳ Qu ->
  eutt RR t u ->
  eutt (fun x y => Qt x /\ Qu y /\ RR x y) t u.
Proof.
  intros HP HQ HEQ.
  bind_ret_r1.
  bind_ret_r2.
  eapply eutt_post_bind_gen; eauto.
  intros.
  by apply eutt_Ret.
Qed.

(* END TO MOVE *)

Definition bid_renaming := bid -> bid.

Definition term_rename (σ: bid_renaming) (t: terminator dtyp): terminator dtyp := match t with
  | TERM_Br v br1 br2 => TERM_Br v (σ br1) (σ br2)
  | TERM_Br_1 br => TERM_Br_1 (σ br)
  | TERM_Switch v default_dest brs => TERM_Switch v (σ default_dest) (map (fun '(x, id) => (x, σ id)) brs)
  | TERM_IndirectBr v brs => TERM_IndirectBr v (map σ brs)
  | TERM_Invoke fnptrval args to_label unwind_label => TERM_Invoke fnptrval args (σ to_label) (σ unwind_label)
  | _ => t
end.

Definition bk_term_rename (σ : bid_renaming) (b: blk): blk := {|
  blk_phis       := b.(blk_phis);
  blk_code       := b.(blk_code);
  blk_term       := term_rename σ b.(blk_term);
  blk_comments   := b.(blk_comments)
|}.

Definition ocfg_term_rename (σ : bid_renaming) (g: ocfg): ocfg := (bk_term_rename σ) <$> g.

Record dom_renaming (σ : bid_renaming) (nFROM : gset bid) (g g': ocfg) : Prop :=
  {
    in_dom : forall id, id ∈ inputs g -> (σ id) ∈ inputs g';
    out_dom : forall id, id ∉ nFROM -> (σ id) = id
  }.

Lemma find_block_some_ocfg_term_rename:
  forall g σ id b, g !! id = Some b ->
  (ocfg_term_rename σ g) !! id = Some (bk_term_rename σ b).
Proof.
  intros g. apply map_ind with (m:=g). now cbn.
  intros * NIN REC * IN.
  unfold ocfg_term_rename. rewrite fmap_insert.
  case (decide (id=i));intros ; now simplify_map_eq.
Qed.

Lemma find_block_none_ocfg_term_rename:
  forall g σ id , g !! id = None -> (ocfg_term_rename σ g) !! id = None.
Proof.
  intros g. apply map_ind with (m:=g). now cbn.
  intros * NIN REC * IN.
  unfold ocfg_term_rename. rewrite fmap_insert.
  case (decide (id=i));intros ; now simplify_map_eq.
Qed.

Lemma inputs_ocfg_term_rename: forall g σ, inputs g = inputs (ocfg_term_rename σ g).
Proof.
  intros g. apply map_ind with (m:=g). now cbn.
  intros ? [] * NIN REC *.
  unfold ocfg_term_rename. unfold inputs, ocfg_term_rename, bk_term_rename in *. rewrite fmap_insert.
  rewrite !dom_insert_L. now rewrite <- REC.
Qed.

Lemma dom_ocfg_term_rename: forall g σ, dom g = dom (ocfg_term_rename σ g).
Proof.
  apply inputs_ocfg_term_rename.
Qed.

Lemma list_map_id {A}: forall (l: list A) (f: A -> A), (forall x, f x = x) -> List.map f l = l.
Proof.
  induction l. trivial. intros. cbn. now rewrite IHl, H.
Qed.


Lemma ocfg_term_rename_id: forall g, ocfg_term_rename id g = g.
Proof.
  apply map_ind. apply fmap_empty.
  intros * NIN REC.
  unfold ocfg_term_rename in *.
  rewrite fmap_insert. rewrite REC.
  replace (bk_term_rename id x) with x. reflexivity.
  destruct x.
  unfold bk_term_rename. cbn. unfold term_rename.
  case_match; trivial. cbn. rewrite list_map_id. trivial.
  now intros []. now rewrite list_map_id.
Qed.


Module Type Theory (LP : LLVMParams.LLVMParams).
Module DT := DenotationTheory.Make LP.
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

(*
paco
----

gpaco
-----
ginit: initialization
gcofix cih: starting a proof by coinduction
guclo L : use a up-to bind proved valid before in lemma L
gstep : we take a step of the endofunction generating the relation
gbase : conclude by coinduction (w.r.t. what is unlocked)

euttG: only for proving [eutt R] goals
-----
einit: initialization
ecofix cih: starting a proof by coinduction
ebind : use up-to bind

*)

Definition denote_ocfg_equiv_cond (g g': ocfg) (nFROM nTO :gset bid) (σ: bid -> bid) :=
  forall origin header,
    header ∉ nTO ->
    origin ∉ nFROM ->
    ⟦g⟧bs (origin, header) ≈ ⟦g'⟧bs (origin, σ header).

Lemma term_rename_eutt :
  forall term σ,
    eutt (sum_rel (λ a b : bid, σ a = b) eq) ⟦ term ⟧t ⟦ term_rename σ term ⟧t.
Proof with try (now apply raise_raise_eutt || now apply raise_raiseUB_eutt || now apply eutt_Ret; auto).
  intros [] ?...
  - destruct v; cbn.
    ibind=; intros ?...
  - destruct v...
    ibind=; intros ?.
    ibind=; intros ?.
    case_match...
    case_match...
  - destruct v...
    ibind=; intros ?.
    ibind=; intros ?.
    case_match...
    ibind with (Forall2 (fun '(x,a) '(y,b) => x = y /\ σ a = b)).
    + apply map_monad_itree_Forall2.
      apply Util.Forall2_forall.
      split.
      symmetry; by apply map_length.
      intros ? [[] ?] [[] ?] IN IN'.
      apply ListUtil.Nth_map_iff in IN' as ([] & ? & ?).
      red in IN,H1 |-.
      rewrite IN in H1; inv H1.
      ibind=; intros ?.
      by apply eutt_Ret.
    + intros * INV.
      unfold lift_err.
      assert (forall b, select_switch u0 default_dest u1 = b ->
                  select_switch u0 (σ default_dest) u2 = match b with | inl b => inl b | inr b => inr (σ b) end).
      {
        clear - INV.
        revert u2 INV.
        induction u1 as [ | [] u1 IH]; intros u2 HIND ? EQ.
        - by apply Forall2_nil_inv_l in HIND; subst.
        - apply Forall2_cons_inv_l in HIND as ([] & l'' & (-> & <-) & HIND & ->).
          subst.
          destruct u0; cbn in *; simplify_eq; try done.
          all: destruct d0; auto.
          all: case_match; auto.
      }

      case_match; specialize (H0 _ eq_refl); rewrite H0.
      apply raise_raise_eutt.
      by apply eutt_Ret; constructor.
Qed.

Lemma bk_phi_rename_eutt :
    forall bk σ from,
      eutt (sum_rel (λ a b : bid, σ a = b) eq) (⟦ bk ⟧b from) (⟦ bk_term_rename σ bk ⟧b from).
Proof.
  intros [] ? ?.
  rewrite denote_block_unfold.
  cbn; repeat setoid_rewrite bind_bind.
  ibind=; intros ?.
  ibind=; intros ?.
  setoid_rewrite bind_ret_l.
  ibind=; intros ?.
  setoid_rewrite bind_ret_l.
  apply term_rename_eutt.
Qed.

Theorem denote_ocfg_equiv (g1 g2 g2' : ocfg) (σ : bid_renaming) (nFROM nTO: gset bid) :
  inputs g2 ∩ inputs g2' ## nFROM -> nFROM ⊆ inputs g2 ∪ inputs g2' ->
  inputs g2' ∖ inputs g2 ⊆ nTO -> nTO ⊆ inputs g2 ∪ inputs g2' -> nTO ## outputs g1 ->
  g1 ##ₘ g2 -> ocfg_term_rename σ g1 ##ₘ g2' ->
  dom_renaming σ nFROM g2 g2' ->
  denote_ocfg_equiv_cond g2 g2' nFROM nTO σ ->
  forall from to' to,
  to' = σ to ->
  to ∉ nTO -> from ∉ nFROM ->
  ⟦g2 ∪ g1⟧bs (from,to) ≈ ⟦g2' ∪ ocfg_term_rename σ g1⟧bs (from, to').
Proof.
  intros nFROMDIS nFROMs nTOsup nTOsub DIS' DIS DISσ [in_dom out_dom] CND.
  einit.
  ecofix cih.
  clear cihH.
  intros * EQσ NINt NINf.
  (* Either we are in the 'visible' graph or not. *)
  case (decide (to ∈ (inputs g2 ∪ inputs g1))) as [tIN'|tNIN']. apply elem_of_union in tIN' as [tIN|tIN]; cycle 1.
  - (* if we enter g1: then process [g1], and get back to the whole thing *)
    assert (σTO: σ to=to). {
      apply out_dom. assert (HNIN: to ∉ inputs g2 ∪ inputs g2'). rewrite elem_of_union. unfold inputs in *.
      rewrite map_disjoint_dom in DIS, DISσ. intros [|]; set_solver. intros ?. apply HNIN. now apply nFROMs.
    }
    pose proof find_block_in_inputs _ tIN as [bk tFIND].
    assert (FIND: (g2 ∪ g1) !! to = Some bk) by now simplify_map_eq.
    rewrite denote_ocfg_in_eq_itree; [| exact FIND].
    pose proof find_block_some_ocfg_term_rename _ σ _ _ tFIND as FINDσ.
    assert (FIND': (g2' ∪ ocfg_term_rename σ g1) !! to' = Some (bk_term_rename σ bk)).
    rewrite EQσ, σTO; now simplify_map_eq.
    rewrite denote_ocfg_in_eq_itree; [| exact FIND'].
    (* Then we start with a first block and then remaining of processing g1 *)
    ebind.
    econstructor.
    eapply has_post_enrich_eutt;
      [apply denote_bk_exits_in_outputs|
        apply denote_bk_exits_in_outputs|
        apply bk_phi_rename_eutt].
    intros ?? (H1 & H2 & H3).
    destruct H3.
    + etau.
      ebase.
      right.
      rewrite EQσ,σTO.
      apply cihL; auto.
      * assert (a1 ∈ outputs g1).
        cbn in *.
        eapply outputs_elem_of; eauto.
        set_solver.
      * eapply not_elem_of_weaken. 2: apply nFROMs. intros toIN. apply elem_of_union in toIN as [toIN|toIN].
        -- unfold inputs in *. apply map_disjoint_dom in DIS. set_solver.
        -- unfold inputs in *. apply map_disjoint_dom in DISσ. rewrite <- dom_ocfg_term_rename in DISσ. set_solver.
    + eret; subst; auto.
  - rewrite (@denote_ocfg_prefix_eq_itree ∅ g2 g1 (g2 ∪ g1) from to); cycle 1; auto.
    symmetry. rewrite <- map_union_assoc. rewrite map_union_comm. apply map_union_empty. 1,2: apply map_disjoint_empty_l.
    rewrite (@denote_ocfg_prefix_eq_itree ∅ g2' (ocfg_term_rename σ g1) (g2' ∪ ocfg_term_rename σ g1) from to'); cycle 1; auto.
    symmetry. rewrite <- map_union_assoc. rewrite map_union_comm. apply map_union_empty. 1,2: apply map_disjoint_empty_l.
    ebind; econstructor.
    + subst to'.
      eapply has_post_enrich_eutt;
        [apply denote_ocfg_exits_all; cbn; auto |
          apply denote_ocfg_exits_all; cbn; auto|
        ].
      apply CND; done.
    + intros ?? ([IN1 NIN1] & [IN2 NIN2] & <-).
      destruct u1; intros; [| eret].
      destruct p as [from2 to2].
      (* We need to know that to2 ∉ inputs g2
        Hence we are back in the first case
      *)
      (* g2 and g2' end with the same destination, so: *)
      assert (NINt2: to2 ∉ inputs g2 ∪ inputs g2') by (cbn in *; set_solver).
      assert (INf2: from2 ∈ inputs g2 ∩ inputs g2').
      by (cbn in *; set_solver).
      assert (to2 ∉ nTO) by (intros H; apply NINt2; now apply nTOsub).
      assert (from2 ∉ nFROM) by set_solver.
      assert (EQσ2: σ to2 = to2). {
        apply out_dom. assert (HNIN: to2 ∉ inputs g2 ∪ inputs g2'). rewrite elem_of_union. unfold inputs in *.
        rewrite map_disjoint_dom in DIS, DISσ. intros [|]; set_solver. intros ?. apply HNIN. now apply nFROMs.
      } {
        case (decide (to2 ∈ inputs g1)) as [t2IN|t2NIN].
        - pose proof find_block_in_inputs _ t2IN as [bk tFIND].
          assert (FIND: (g2 ∪ g1) !! to2 = Some bk) by now simplify_map_eq.
          rewrite denote_ocfg_in_eq_itree; [| exact FIND].
          pose proof find_block_some_ocfg_term_rename _ σ _ _ tFIND as FINDσ.
          assert (FIND': (g2' ∪ ocfg_term_rename σ g1) !! to2 = Some (bk_term_rename σ bk)) by now simplify_map_eq.
          rewrite denote_ocfg_in_eq_itree; [| exact FIND'].
          ebind.
          econstructor.
          eapply has_post_enrich_eutt;
          [apply denote_bk_exits_in_outputs|
          apply denote_bk_exits_in_outputs|
          apply bk_phi_rename_eutt].
          intros ?? (? & ? & H3).
          destruct H3.
          + etau.
            ebase.
            right.
            apply cihL; auto.
            assert (a1 ∈ outputs g1).
            cbn in *.
            eapply outputs_elem_of; eauto.
            set_solver.
          + eret; subst; auto.
        - rewrite denote_ocfg_nin_eq_itree.
          rewrite denote_ocfg_nin_eq_itree.
          eret.
          all: apply free_out_of_inputs.
          all: rewrite inputs_union; trivial.
          rewrite <- inputs_ocfg_term_rename.
          all: set_solver.
      }
  - assert (σTO: σ to = to). {
      assert (H: to ∉ inputs g2'). {
        intros ?. apply NINt. apply nTOsup. set_solver.
      } assert (H0: to ∉ inputs g2 ∪ inputs g2') by set_solver.
      apply out_dom. intros ?. apply H0. now apply nFROMs.
    }
    subst; rewrite σTO.
    rewrite denote_ocfg_nin_eq_itree.
    rewrite denote_ocfg_nin_eq_itree.
    eret.
    all: apply free_out_of_inputs.
    all: rewrite inputs_union; trivial.
    rewrite <- inputs_ocfg_term_rename.
    set_solver.
Qed.

End Theory.

Module Make (LP : LLVMParams.LLVMParams) : Theory LP.
  Include Denotation.Theory LP.
End Make.