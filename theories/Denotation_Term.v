(** This file contains the tools to prove the correctness of the block fusion optimization.
    It relies on the garantees given by the [BlockFusion] pattern. *)

From Vellvm Require Import Syntax ScopeTheory Semantics Theory Tactics Denotation DenotationTheory.
From ITree Require Import ITree Eq HeterogeneousRelations.
From Pattern Require Import Base Patterns BlockFusion.
From Paco Require Import paco.
(* Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
(* Import TopLevelBigIntptr InterpretationStack. *)
(* Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Patterns. *)
From stdpp Require Import prelude fin_maps.
Import Head Focus Block Patterns gmap.
(* Set Implicit Arguments. *)
(* Block Fusion *)

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

Definition fusion (idA : block_id) (A B: blk): blk := {|
  blk_phis       := A.(blk_phis);
  blk_code       := fusion_code idA A B;
  blk_term       := B.(blk_term);
  blk_comments   := fusion_comments A B
|}.

(* Import SemNotations. *)
(* todo better representation*)
Definition bk_renaming := bid -> bid.

(* Definition exps_rename σ (id: bid) e (φ: gmap bid (exp dtyp)) := {[σ id := e]} ∪ φ.

Definition phi_rename (σ : bk_renaming) (ϕ:  phi dtyp): phi dtyp :=
  match ϕ with
    | Phi τ exps => Phi τ (map_fold (exps_rename σ) ∅ exps)
  end. *)

Definition term_rename (σ: bk_renaming) (t: terminator dtyp): terminator dtyp := match t with
  | TERM_Br v br1 br2 => TERM_Br v (σ br1) (σ br2)
  | TERM_Br_1 br => TERM_Br_1 (σ br)
  | TERM_Switch v default_dest brs => TERM_Switch v (σ default_dest) (map (fun '(x, id) => (x, σ id)) brs)
  | TERM_IndirectBr v brs => TERM_IndirectBr v (map σ brs)
  | TERM_Invoke fnptrval args to_label unwind_label => TERM_Invoke fnptrval args (σ to_label) (σ unwind_label)
  | _ => t
end.

Definition bk_term_rename (σ : bk_renaming) (b: blk): blk := {|
  blk_phis       := b.(blk_phis);
  blk_code       := b.(blk_code);
  blk_term       := term_rename σ b.(blk_term);
  blk_comments   := b.(blk_comments)
|}.

Definition ocfg_rename (σ : bk_renaming) (g: ocfg): ocfg := (bk_term_rename σ) <$> g.

Record dom_renaming (σ : bk_renaming) (s : gset bid) (g g': ocfg) : Prop :=
  {
    in_dom : forall id, id ∈ inputs g -> (σ id) ∈ inputs g';
    out_dom : forall id, id ∉ s -> (σ id) = id
  }.

Module Type Theory (LP : LLVMParams.LLVMParams).
  Module DT := DenotationTheory.Make LP.
  Import DT.
  Import DT.D.
  Import LP.

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

Import ITree.


Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).
End eutt_Notations.
Import eutt_Notations.

(* About denote_ocfg_prefix. *)

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

Import SemNotations.
Import MonadNotation.
Import Events.DV.

Lemma denote_ocfg_prefix_eq_itree:
  forall (prefix bks' postfix : ocfg) [bks : ocfg] (from to : bid),
    bks = prefix ∪ bks' ∪ postfix ->
    ⟦ bks ⟧bs (from, to) ≅
    x_ <- ⟦ bks' ⟧bs (from, to);
    match x_ with
      | inl x => ⟦ bks ⟧bs x
      | inr x => Ret (inr x)
  end.
Proof.
Admitted.

Definition denote_ocfg_equiv_cond (g g': ocfg) (nFROM nTO :gset bid) (σ: bid -> bid) :=
  forall origin header,
    header ∈ inputs g ->
    header ∉ nTO ->
    origin ∉ nFROM ->
    ⟦g⟧bs (origin, header) ≈ ⟦g'⟧bs (origin, σ header).

Lemma find_block_some_ocfg_rename: forall g σ id b, g !! id = Some b -> (ocfg_rename σ g) !! id = Some (bk_term_rename σ b).
Proof.
  intros g. apply map_ind with (m:=g). now cbn.
  intros * NIN REC * IN.
  unfold ocfg_rename. rewrite fmap_insert.
  case (decide (id=i));intros ; now simplify_map_eq.
Qed.

Lemma find_block_none_ocfg_rename:
  forall g σ id , g !! id = None -> (ocfg_rename σ g) !! id = None.
Proof.
  intros g. apply map_ind with (m:=g). now cbn.
  intros * NIN REC * IN.
  unfold ocfg_rename. rewrite fmap_insert.
  case (decide (id=i));intros ; now simplify_map_eq.
Qed.

Lemma inputs_ocfg_rename: forall g σ, inputs g = inputs (ocfg_rename σ g).
Proof.
  intros g. apply map_ind with (m:=g). now cbn.
  intros ? [] * NIN REC *.
  unfold ocfg_rename. unfold inputs, ocfg_rename, bk_term_rename in *. rewrite fmap_insert.
  rewrite !dom_insert_L. cbn. cbn. now rewrite <- REC.
Qed.

Lemma dom_ocfg_rename: forall g σ, dom g = dom (ocfg_rename σ g).
Proof.
  apply inputs_ocfg_rename.
Qed.

(*

block fusion: je rentrais par a, je rentre maintenant par b

b = σ a

σ : renaming map

 *)


Lemma raise_raise_eutt : forall {E A} Q `{FailureE -< E} s,
    eutt Q (@raise E A _ s) (@raise E A _ s).
Admitted.

Lemma raise_raiseUB_eutt : forall {E A} Q `{UBE -< E} s,
    eutt Q (@raiseUB E _ A s) (@raiseUB E _ A s).
Admitted.

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
    ibind with (Forall2 (fun '(_,a) '(_,b) => σ a = b)).
    + admit. (* TODO YZ *)
    + intros * INV.
      admit. (* TODO YZ *)
Admitted.

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
Import PostConditions.

Theorem denote_ocfg_equiv (g1 g2 g2' : ocfg) (σ : bk_renaming) (nFROM nTO: gset bid) :
  inputs g2 ∩ inputs g2' ## nFROM -> nFROM ⊆ inputs g2 ∪ inputs g2' -> inputs g2' ∖ inputs g2 ⊆ nTO -> nTO ⊆ inputs g2 ∪ inputs g2' ->
  nTO ## outputs g1 -> g1 ##ₘ g2 -> ocfg_rename σ g1 ##ₘ g2' ->
  dom_renaming σ nFROM g2 g2' ->
  denote_ocfg_equiv_cond g2 g2' nFROM nTO σ ->
  forall from to' to,
  to' = σ to ->
  to ∉ nTO -> from ∉ nFROM ->
  ⟦g1 ∪ g2⟧bs (from,to) ≈ ⟦ocfg_rename σ g1 ∪ g2'⟧bs (from, to').
Proof.
  intros nFROMDIS nFROMs nTOsup nTOsub DIS' DIS DISσ [in_dom out_dom] CND.
  einit.
  ecofix cih.
  clear cihH.
  intros * EQσ NINt NINf.
  (* Either we are in the 'visible' graph or not. *)
  case (decide (to ∈ (inputs g1 ∪ inputs g2))) as [tIN'|tNIN']. apply elem_of_union in tIN' as [tIN|tIN].
  - (* if we enter g1: then process [g1], and get back to the whole thing *)
    assert (σTO: σ to=to). {
      apply out_dom. assert (HNIN: to ∉ inputs g2 ∪ inputs g2'). rewrite elem_of_union. unfold inputs in *.
      rewrite map_disjoint_dom in DIS, DISσ. intros [|]; set_solver. intros ?. apply HNIN. now apply nFROMs.
    }
    pose proof find_block_in_inputs _ tIN as [bk tFIND].
    assert (FIND: (g1 ∪ g2) !! to = Some bk) by now simplify_map_eq.
    rewrite denote_ocfg_in_eq_itree; [| exact FIND].
    pose proof find_block_some_ocfg_rename _ σ _ _ tFIND as FINDσ.
    assert (FIND': (ocfg_rename σ g1 ∪ g2') !! to' = Some (bk_term_rename σ bk)).
    rewrite EQσ, σTO; now simplify_map_eq.
    rewrite denote_ocfg_in_eq_itree; [| exact FIND'].
    (* Then we start with a first block and then remaining of processing g1 *)
    ebind.
    econstructor; [apply bk_phi_rename_eutt |].
    intros ?? [].
    + etau.
      ebase.
      right.
      rewrite EQσ,σTO.
      apply cihL; auto.
      * assert (a1 ∈ outputs g1) by admit. (* TODO YZ meta-theory has_post/eutt *)
        set_solver.
      * eapply not_elem_of_weaken. 2: apply nFROMs. intros toIN. apply elem_of_union in toIN as [toIN|toIN].
        -- unfold inputs in *. apply map_disjoint_dom in DIS. set_solver.
        -- unfold inputs in *. apply map_disjoint_dom in DISσ. rewrite <- dom_ocfg_rename in DISσ. set_solver.
    + eret; subst; auto.
  - rewrite (@denote_ocfg_prefix_eq_itree g1 g2 ∅ (g1 ∪ g2) from to); cycle 1.
    symmetry. apply map_union_empty.
    rewrite (@denote_ocfg_prefix_eq_itree (ocfg_rename σ g1) g2' ∅ (ocfg_rename σ g1 ∪ g2') from to'); cycle 1.
    symmetry. apply map_union_empty.
    ebind; econstructor.
    + subst to'; apply CND; done.
    + intros ?? <-.
      case u1; intros; [| eret].
      destruct p as [from2 to2].
      (* We need to know that to2 ∉ inputs g2
         Hence we are back in the first case
      *)
      (* g2 and g2' end with the same destination, so: *)
      assert (NINt2: to2 ∉ inputs g2 ∪ inputs g2') by admit.
      assert (INf2: from2 ∈ inputs g2 ∩ inputs g2') by admit.
      assert (to2 ∉ nTO) by (intros H; apply NINt2; now apply nTOsub).
      assert (from2 ∉ nFROM) by set_solver.
      assert (EQσ2: σ to2 = to2). {
        apply out_dom. assert (HNIN: to2 ∉ inputs g2 ∪ inputs g2'). rewrite elem_of_union. unfold inputs in *.
        rewrite map_disjoint_dom in DIS, DISσ. intros [|]; set_solver. intros ?. apply HNIN. now apply nFROMs.
      } {
        case (decide (to2 ∈ inputs g1)) as [t2IN|t2NIN].
        - pose proof find_block_in_inputs _ t2IN as [bk tFIND].
          assert (FIND: (g1 ∪ g2) !! to2 = Some bk) by now simplify_map_eq.
          rewrite denote_ocfg_in_eq_itree; [| exact FIND].
          pose proof find_block_some_ocfg_rename _ σ _ _ tFIND as FINDσ.
          assert (FIND': (ocfg_rename σ g1 ∪ g2') !! to2 = Some (bk_term_rename σ bk)) by now simplify_map_eq.
          rewrite denote_ocfg_in_eq_itree; [| exact FIND'].
          ebind.
          econstructor; [apply bk_phi_rename_eutt |].
          intros ?? [].
          + etau.
            ebase.
            right.
            apply cihL; auto.
            assert (a1 ∈ outputs g1) by admit. (* TODO YZ meta-theory has_post/eutt *)
            set_solver.
          + eret; subst; auto.
        - rewrite denote_ocfg_nin_eq_itree.
          rewrite denote_ocfg_nin_eq_itree.
          eret.
          all: apply free_out_of_inputs.
          all: rewrite inputs_union; trivial.
          rewrite <- inputs_ocfg_rename.
          all: set_solver.
      }
  -
    assert (σTO: σ to = to). {
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
    rewrite <- inputs_ocfg_rename.
    set_solver.
Admitted.

Definition σfusion idA idB := fun (id: bid) => if decide (id=idA) then idB else id.

Theorem Denotation_BlockFusion_correct (G G':ocfg) idA A idB B f to:
  let σ := σfusion idA idB in
  to <> idB ->
  f <> idA ->
  (idA, A, (idB, B, G')) ∈ (MatchAll (BlockFusion □) G) ->
  ⟦ G' ∪ ({[idA:=A;idB:=B]}) ⟧bs (f, to) ≈
  ⟦ ocfg_rename σ G' ∪ {[idB:=fusion idA A B]} ⟧bs (f, σ to).
Proof.
  intros * ineq1 ineq2 IN.
  apply Pattern_BlockFusion_correct in IN as (G1 & IN & FUS); auto.
  apply Pattern_Graph_correct in IN; subst G1.
  destruct FUS as [EQ LUA LUB PRED SUCC].
  assert (BNIN: idB ∉ outputs G') by admit.
  apply denote_ocfg_equiv with (nFROM:={[idA]}) (nTO:={[idB]}); auto; unfold inputs in *.
    * rewrite dom_insert_L, !dom_singleton_L.
      replace ({[idA; idB]} ∩ {[idB]}) with ({[idB]}: gset bid) by set_solver.
      apply disjoint_singleton_l. now apply not_elem_of_singleton.
    * rewrite dom_insert_L. apply elem_of_subseteq_singleton. set_solver.
    * rewrite dom_insert_L, !dom_singleton_L.
      replace ({[idB]} ∖ {[idA; idB]}) with (∅: gset bid) by set_solver.
      apply empty_subseteq.
    * rewrite dom_insert_L, !dom_singleton_L. apply elem_of_subseteq_singleton. set_solver.
    * now apply disjoint_singleton_l.
    * apply map_disjoint_insert_r. split. now simplify_map_eq.
      apply map_disjoint_singleton_r. now simplify_map_eq.
    * apply map_disjoint_singleton_r. apply find_block_none_ocfg_rename. now simplify_map_eq.
    * split; intros id H.
      + unfold inputs in *. rewrite dom_insert_L in H. rewrite dom_singleton_L in H |- *.
        subst σ. unfold σfusion. case_match; set_solver.
      + subst σ. unfold σfusion. assert (id ≠ idA) by now apply not_elem_of_singleton in H. now case_match.
    * unfold denote_ocfg_equiv_cond.
      intros * H1 H2 H3.
      assert (header = idA).
      {
        clear - H2 H1.
        unfold inputs in *.
        rewrite dom_insert_L, !dom_singleton_L in H1.
        admit.
      }
      subst header.
      subst σ. unfold σfusion.
      case_match; try done.
      simplify_eq.
      rewrite ?denote_ocfg_in; try by simplify_map_eq.
      destruct A.
Arguments denote_code : simpl never.
Arguments denote_phis : simpl never.
Arguments promote_phis : simpl never.
Opaque denote_phis.
Opaque denote_code.

cbn.
setoid_rewrite bind_bind.
ibind=; intros ?.
setoid_rewrite bind_bind.
rewrite denote_code_app; setoid_rewrite bind_bind.
ibind=; intros ?.

      assert (LEM: forall t id,
                 terminator_outputs t = {[id]} ->
                 ⟦ t ⟧t ≈ Ret (inl id)).
      admit.
      apply LEM in SUC.
      rewrite SUC, bind_ret_l.
      rewrite ?denote_ocfg_in; try by simplify_map_eq.
      destruct B.
      cbn.

      rewrite denote_code_app; setoid_rewrite bind_bind.
      ibind with eq.
      {
        admit.
      }
      intros ? ? <-.
      rewrite bind_bind.
      ibind=.
      intros ?; ibind=.
      intros [|]; [| reflexivity].
    (* Note: in all due generality, could loop back on itself.
       Need a proof by coinduction.
     *)
      admit.


    * now apply not_elem_of_singleton.
    * now apply not_elem_of_singleton.
Admitted.

End Theory.
