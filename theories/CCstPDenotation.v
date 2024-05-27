(** This file contains the proof of correctness of the Conditional Constant Propagation optimization.
    It relies on the garantees given by the [CCstP] pattern and on proofs form the [Denotation] file. *)

From Vellvm Require Import Syntax ScopeTheory Semantics Theory Tactics Denotation DenotationTheory.
From ITree Require Import ITree Eq HeterogeneousRelations.
From Pattern Require Import Base Patterns Denotation CCstP.
From Paco Require Import paco.
From stdpp Require Import prelude fin_maps strings.
Import List Head Focus Block Patterns gmap Utils.Monads PostConditions Pattern.Denotation ITree.

Definition term_change (t: terminator dtyp) (f: analysis): terminator dtyp := match t with
  | TERM_Br e l r => match f e with 
    | One => TERM_Br_1 l
    | Zero => TERM_Br_1 r
    | _ => t
    end
  | _ => t
end.

Definition rewrite_term (b: blk) (f: analysis): blk := {|
  blk_phis       := b.(blk_phis);
  blk_code       := b.(blk_code);
  blk_term       := term_change b.(blk_term) f;
  blk_comments   := b.(blk_comments)
|}.

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

Definition correct_analysis (f: analysis) := forall t e,
  (f (t,e) = One -> denote_exp (Some t) e ≈ Ret (UVALUE_I1 VellvmIntegers.Int1.one)) /\
  (f (t,e) = Zero -> denote_exp (Some t) e ≈ Ret (UVALUE_I1 VellvmIntegers.Int1.zero)).

Lemma rewrite_term_correct {S} f G idB (B: blk) X (P: Pattern S):
  correct_analysis f -> (idB, B, X) ∈ (MatchAll (CCstP f P) G) ->
  denote_ocfg_equiv_cond {[idB := B]} {[idB := rewrite_term B f]} ∅ ∅ id.
Proof.
  intros AN IN.
  apply Pattern_CCstP_correct in IN as (G0 & _ & SEM).
  destruct SEM as [EQ IN (e & l & r & EQt & AN')].
  unfold denote_ocfg_equiv_cond.
  einit.
  ecofix cih.
  clear cihH.
  intros fr to _ _.
  case (decide (to=idB)) as [->|NEQ].
  - rewrite ?denote_ocfg_in_eq_itree; try by simplify_map_eq.
    destruct B as [phisB codeB termB cB].
    remember {| blk_phis := phisB; blk_code := codeB; blk_term := termB; blk_comments := cB |} as B.
    cbn.
    setoid_rewrite bind_bind.
    ebind. econstructor; [reflexivity|]. intros [] ? <-.
    setoid_rewrite bind_bind. 
    ebind. econstructor; [reflexivity|]. intros [] ? <-.
    rewrite !EQt.
    ebind. econstructor.  { 
      destruct e as [t e]. pose proof AN t e as [AN1 AN0].
      destruct AN' as [AN'|AN']; cbn; rewrite AN'; [apply AN0 in AN'|apply AN1 in AN'];
      rewrite AN', bind_ret_l;cbn; rewrite bind_ret_l; reflexivity.
    }
    intros [] ? <-.
    * etau. ebase. right. apply cihL; set_solver.
    * eret.
  - rewrite ?denote_ocfg_nin_eq_itree; now simplify_map_eq.
Qed.

Theorem Denotation_CCstP_correct {S} f G idB B P (X: S) fr to:
  correct_analysis f -> (idB, B, X) ∈ (MatchAll (CCstP f P) G) ->
  ⟦ G ⟧bs (fr, to) ≈ ⟦ <[idB := rewrite_term B f]>(delete idB G) ⟧bs (fr, to).
Proof.
  intros AN IN.
  pose proof IN as IN0.
  pose proof AN as AN0.
  apply Pattern_CCstP_correct in IN as (G' & _ & SEM).
  destruct SEM as [EQ IN (e & l & r & EQt & AN')].
  pose proof insert_union_singleton_l G' idB (rewrite_term B f) as EQ''.
  assert (EQ': G = {[idB := B]} ∪ G'). {
    simplify_map_eq. rewrite <- insert_union_singleton_l. now rewrite insert_delete.
  } 
  pose proof ocfg_term_rename_id G' as Hσ.
  rewrite <- EQ, EQ'', <- Hσ, EQ'.
  clear EQ'' EQ'.
  eapply denote_ocfg_equiv.
  - apply disjoint_empty_r.
  - apply empty_subseteq.
  - unfold inputs. rewrite !dom_singleton_L. rewrite difference_diag_L. apply empty_subseteq.
  - apply empty_subseteq.
  - apply disjoint_empty_l.
  - rewrite EQ. apply map_disjoint_insert_r. split. now simplify_map_eq.
    apply map_disjoint_empty_r.
  - rewrite Hσ, EQ. apply map_disjoint_insert_r. split. now simplify_map_eq.
    apply map_disjoint_empty_r.
  - split.
    * intros id' IN'. cbn.
      unfold inputs in *. now rewrite dom_singleton_L in IN' |- *.
    * now cbn.
  - eapply rewrite_term_correct; [trivial|apply IN0].
  - now cbn.
  - set_solver.
  - set_solver.
Qed.

End Theory.