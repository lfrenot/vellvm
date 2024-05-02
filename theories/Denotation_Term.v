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

Definition fusion_code (A B: blk): code dtyp := A.(blk_code) ++ B.(blk_code).

Definition fusion_comments (A B: blk) :=
  match (A.(blk_comments), B.(blk_comments)) with
    | (Some cA, Some cB) => Some (cA++cB)
    | (Some cA, _) => Some cA
    | (_, Some cB) => Some cB
    | (_, _) => None
  end.

Definition fusion (A B: blk): blk := {|
  blk_phis       := B.(blk_phis);
  blk_code       := fusion_code A B;
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

Record dom_renaming (σ : bk_renaming) (from to : gset bid) : Prop :=
  {
    in_dom : forall id, id ∈ from -> (σ id) ∈ to;
    out_dom : forall id, id ∉ from -> (σ id) = id
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

Definition denote_ocfg_equiv_cond (g1 g2 g2': ocfg) (nTO :gset bid) (σ: bid -> bid) :=
  forall origin header,
    header ∉ nTO ->
    eutt (Logic.eq)
      (⟦g2 ⟧bs (origin, header))
      (⟦g2'⟧bs (origin, σ header)).


Lemma find_block_some_ocfg_rename: forall g σ id b, g !! id = Some b -> (ocfg_rename σ g) !! id = Some (bk_term_rename σ b).
Proof.
  intros g. apply map_ind with (m:=g). now cbn.
  intros * NIN REC * IN.
  unfold ocfg_rename. rewrite fmap_insert.
  case (decide (id=i));intros ; now simplify_map_eq.
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

Theorem denote_ocfg_equiv (g1 g2 g2' : ocfg) (σ : bk_renaming) :
  let nTO := inputs g2 ∖ outputs g1 in
  let nFROM := inputs g2 ∩ outputs g1 in
  g1 ##ₘ g2 -> ocfg_rename σ g1 ##ₘ g2' ->
  dom_renaming σ nTO (inputs g2') ->
  denote_ocfg_equiv_cond g1 g2 g2' nTO σ ->
  forall from to' to,
  to' = σ to ->
  to ∉ nTO -> from ∉ nFROM ->
  ⟦g1 ∪ g2⟧bs (from,to) ≈ ⟦ocfg_rename σ g1 ∪ g2'⟧bs (from, to').
Proof.
  intros nTO nFROM.
  einit.
  ecofix cih.
  clear cihH.
  intros DIS DISσ [in_dom out_dom] CND * EQσ NINt NINf.
  (* pose proof cihL EQ CND. *)
  (* Either we are in the 'visible' graph or not. *)
  case (decide (to ∈ (inputs g1 ∪ inputs g2))) as [tIN'|tNIN']. apply elem_of_union in tIN' as [tIN|tIN].
  - (* if we enter g1: then process [g1], and get back to the whole thing *)
    assert (σTO: σ to=to) by now apply out_dom.
    pose proof find_block_in_inputs _ tIN as [bk tFIND].
    assert (FIND: (g1 ∪ g2) !! to = Some bk) by now simplify_map_eq.
    rewrite denote_ocfg_in_eq_itree; [| exact FIND].
    pose proof find_block_some_ocfg_rename _ σ _ _ tFIND as FINDσ.
    assert (FIND': (ocfg_rename σ g1 ∪ g2') !! to' = Some (bk_term_rename σ bk)). rewrite EQσ, σTO; now simplify_map_eq.
    rewrite denote_ocfg_in_eq_itree; [| exact FIND'].

  (* Then we start with a first block and then remaining of processing g1 *)
    (* subst. *)
    ebind.
    econstructor; [apply bk_phi_rename_eutt |].
    intros ?? [].
    + etau.
      ebase.
      right.
      rewrite EQσ,σTO.
      apply cihL; auto.
      constructor; auto.
      subst nTO.
      * assert (a1 ∈ outputs g1) by admit. (* TODO YZ meta-theory has_post/eutt *)
        set_solver.
      * admit. (* TODO Leon *)

    + eret; subst; auto.
  -
    (* assert (to ∈ outputs g1 /\ to ∈ inputs g2) as [tINo tINi] by (now apply elem_of_intersection). *)
    (* generalize tIN; intros tmp; apply cap_correct in tmp as [tINo tINi]. *)
    rewrite (@denote_ocfg_prefix_eq_itree g1 g2 ∅ (g1 ∪ g2) from to); cycle 1.
    symmetry. apply map_union_empty.
    (* set_solver. *)
    rewrite (@denote_ocfg_prefix_eq_itree (ocfg_rename σ g1) g2' ∅ (ocfg_rename σ g1 ∪ g2') from to'); cycle 1.
    symmetry. apply map_union_empty.
    (* set_solver. *)
    ebind; econstructor.
    + subst to'; apply CND; done.
    + intros ?? <-.
      case u1; intros; [| eret].
      destruct p as [new_from new_to].
      (* We need to know that new_to ∉ inputs g2
         Hence we are back in the first case
       *)
      assert (new_to ∉ inputs g2) by admit.
      admit.
  - assert (to = to') by admit.
    subst; rewrite <- H.
    rewrite denote_ocfg_nin_eq_itree.
    rewrite denote_ocfg_nin_eq_itree.
    eret.
    admit.
    admit.

Admitted.

Definition σfusion idA idB := fun (id: bid) => if decide (id=idB) then idA else id.

Theorem Denotation_BlockFusion_correct (G G':ocfg) idA A idB B f to:
  let σ := σfusion idA idB in
  to <> idB ->
  f <> idA ->
  (idA, A, (idB, B, G')) ∈ (MatchAll (BlockFusion □) G) ->
  ⟦ G' ∪ ({[idA:=A]} ∪ {[idB:=B]}) ⟧bs (f, to) ≈
  ⟦ ocfg_rename σ G' ∪ {[idA:=fusion A B]} ⟧bs (σ f, to).
Proof.
  intros * ineq1 ineq2 IN.
  apply Pattern_BlockFusion_correct in IN as (G1 & IN & FUS); auto.
  apply Pattern_Graph_correct in IN; subst G1.
  destruct FUS as [EQ LUA LUB PRED SUCC].
  apply denote_ocfg_equiv; auto.
  - unfold inputs. Search predecessors. Search outputs.

  (* set (g := map_cfg_to_ocfg G).
  match goal with
    |- context[map_cfg_to_ocfg ?g] => set (g' := map_cfg_to_ocfg g)
  end. 
  set (σ := fun id => if eqb id (blk_id B) then blk_id A else id).
  assert (EQg: g = rm_bk A (rm_bk B g) ++ [A;B]).
  admit.
  assert (EQg': g' = ocfg_rename σ (rm_bk A (rm_bk B g)) ++ [fusion A B]).
  admit.
  rewrite EQg, EQg'.
  apply denote_ocfg_equiv.
  - admit.
  - admit.
  - admit.
  - admit.
  - intros from header. rewrite cap_correct. intros [hINo hINi]. apply find_block_in_inputs in hINi as [b bIN].
    (* rewrite denote_ocfg_unfold_in; cycle 1.
    apply bIN.
    rewrite denote_ocfg_unfold_in; cycle 1.
    assert (bIN': find_block [fusion A B] header = Some b). admit. apply bIN'. *)
    admit.
  - admit. *)
Admitted.

End DenotationTheory.

*)
