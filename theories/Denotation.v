From TwoPhase Require Import Syntax ScopeTheory Semantics Theory Tactics.
From ITree Require Import ITree Eq HeterogeneousRelations.
From Pattern Require Import IdModule MapCFG Patterns BlockFusion.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import TopLevelBigIntptr InterpretationStack.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Patterns.
(* Set Implicit Arguments. *)
(* Denotation definitions *)

Definition ocfg_to_map_cfg (g: ocfg) := List.fold_right (fun b => add_id b) empty g.

Definition map_cfg_to_ocfg (g : map_cfg): ocfg := List.map snd (elements g).

Definition denotation_map_cfg (g : map_cfg) fto :ITreeDefinition.itree instr_E (bid * bid + uvalue) := (denote_ocfg (map_cfg_to_ocfg g)) fto.

(* Block Fusion *)

Definition fusion_code (A B: blk): code dtyp. Admitted.

Definition fusion_comments (A B: blk): option (list String.string). Admitted.

Definition fusion (A B: blk): blk :=
  mk_block A.(blk_id) A.(blk_phis) (fusion_code A B) B.(blk_term) (fusion_comments A B).

Import SemNotations.
Import SetNotations.
(* todo better representation*)
Definition bk_renaming := bid -> bid.
Definition bk_rename (σ : bk_renaming) : ocfg -> ocfg.
Admitted.

Record dom_renaming (σ : bk_renaming) (from to : list bid) : Prop :=
  {
    in_dom : forall id, List.In id from -> List.In (σ id) to;
    out_dom : forall id, ~ List.In id from -> (σ id) = id
  }.

(* Nodes that may exit the graph *)
Definition outs (g : ocfg) : list bid.
Admitted.

Theorem foo (g1 g2 g2' : ocfg) (header : bid) (σ : bk_renaming) from to :
  incl (outputs g1 +++ inputs g2) [header] ->
  dom_renaming σ (outs g2) (outs g2') ->
  (forall origin,
      eutt (sum_rel (fun '(from,to) '(from', to') => from' = σ from /\ to = to') Logic.eq)
        (⟦g2⟧bs (origin, header)) (⟦g2'⟧bs (origin, header))) ->
  List.In to (header ::: inputs g1) ->
  ⟦g1 ++ g2⟧bs (from,to) ≈ ⟦bk_rename σ g1 ++ g2'⟧bs (from, to).
Proof.
  intros * INCL DOMσ EQ IN.
Admitted.

Lemma bar G G' fto :
  ⟦map_cfg_to_ocfg G⟧bs fto ≈ ⟦map_cfg_to_ocfg G'⟧bs fto ->
  denotation_map_cfg G fto ≈ denotation_map_cfg G' fto.
Admitted.

Lemma blk_dec : forall x y : blk, {x = y} + {x <> y}.
Admitted.
Definition rm_bk := List.remove blk_dec.

Import DenotationTheoryBigIntptr.

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

Ltac solve_find_block :=
  cbn;
  match goal with
  (* If the [ocfg] contains a single block, we are done exactly if it has the id we are looking for *)
    | |- find_block [_] _ = _ => apply find_block_eq; reflexivity
  (* Otherwise, if the [ocfg] has a head block, we: *)
(*      - first check if that's the one we are looking for *)
(*      - otherwise dismiss it, focus our well-formedness hypothesis similarly, and continue recursively. *)
(*      - if it is instead built by appending two sub-graphs, we call ourselves recursively in each branch, *)
(*      and don't forget to shape the well-formedness hypothesis in each case beforehand. *)
(*    *)
    | h: wf_ocfg_bid _ |- find_block (_ :: _) _ = _ =>
      first [apply find_block_eq; reflexivity |
             apply find_block_tail_wf; [eassumption | apply wf_ocfg_bid_cons in h; solve_find_block]]
    | h: wf_ocfg_bid _ |- find_block (_ ++ _) _ = _ =>
      first [apply find_block_app_l_wf; [eassumption | apply wf_ocfg_bid_app_l in h; solve_find_block] |
             apply find_block_app_r_wf; [eassumption | apply wf_ocfg_bid_app_r in h; solve_find_block]]
  end.

Ltac vjmp :=
  rewrite denote_ocfg_unfold_in; cycle 1;
  [match goal with
   | h: hidden_cfg _ |- _ => inv h
   | h: visible_cfg _ |- _ => inv h
   | _ => idtac
   end;
   cbn; rewrite ?convert_typ_ocfg_app;
   try solve_find_block |].

Import ITree.
Import ITreeNotations.


Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).
End eutt_Notations.
Import eutt_Notations.

Theorem Denotation_BlockFusion_correct (G G' G'':map_cfg) A B f to:
  wf_map_cfg G -> to <> B.(blk_id) -> f <> A.(blk_id) ->
  (A, (B, G')) ∈ (MatchAll (BlockFusion □) G) ->
  denotation_map_cfg G (f, to) ≈
  denotation_map_cfg (update G' (single (fusion A B))) (f, to).
Proof.
  intros * WF ineq1 ineq2 IN.
  apply Pat_BlockFusion_correct in IN as (G1 & IN & FUS); auto.
  apply Pat_Graph_correct in IN; subst.
  destruct FUS as (-> & EQ & LUA & LUB & PRED & SUCC).
  apply bar.
  set (g := map_cfg_to_ocfg G).
  match goal with
    |- context[map_cfg_to_ocfg ?g] => set (g' := map_cfg_to_ocfg g)
  end.
  set (σ := fun id => if eqb id (blk_id B) then blk_id A else id).
  assert (EQg: g = rm_bk A (rm_bk B g) ++ [A;B]).
  admit.
  assert (EQg': g' = bk_rename σ (rm_bk A (rm_bk B g)) ++ [fusion A B]).
  admit.
  rewrite EQg, EQg'.
  apply foo with (header := blk_id A).

  cbn.
  - admit.
  - admit.
  - intros from.
    rewrite denote_ocfg_unfold_in; cycle 1.
    apply find_block_eq; reflexivity.
    rewrite denote_ocfg_unfold_in; cycle 1.
    apply find_block_eq; reflexivity.
    admit.

  - admit.

Admitted.
