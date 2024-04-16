From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule MapCFG Head Focus Patterns.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Patterns.

Notation exp := (texp dtyp).

Inductive Analysis_1 : Type :=
  | Top
  | Bottom
  | Zero
  | One
.

Notation T := Top.
Notation "⊥" := Bottom.

Definition analysis {S} := S -> Analysis_1.

Definition fixed_branch (f:analysis) (b: blk) := match b.(blk_term) with
  | TERM_Br e _ _ => match f e with | T | ⊥ => false | _ => true end
  | _ => false
end.

Definition CCstP {S} f (P:Pattern S) := (Branch P) when (fun '(B,_,_,_) => fixed_branch f B).

Record CCstP_sem f (B: blk) G G' := {
  WF: wf_map_cfg G';
  EQ: G' = remove_id B G;
  MT: MapsTo_id B G;
  AN: exists e l r, B.(blk_term) = TERM_Br e l r /\ (f e = Zero \/ f e = One)
}.

Lemma Pattern_CCstP_correct {S}: forall f G B P (s:S), wf_map_cfg G ->
    (exists l r, (B, l, r, s) ∈ (MatchAll (CCstP f P) G)) <->
    exists G', s ∈ (MatchAll P G') /\ CCstP_sem f B G G'.
Proof.
  unfold CCstP. intros * WF. split.
  - intros [l [r H]].
    apply Pattern_When_correct in H as [H AN]. unfold fixed_branch in AN.
    apply Pattern_Branch_correct in H as [G' [[EQ [e BR]] H]]; trivial.
    exists G'. split; trivial.
    rewrite BR in AN. repeat split; trivial. 2: exists e, l, r; split; trivial.
    * rewrite EQ. now apply remove_wf_map_cfg.
    * remember (f e) as a. induction a; try discriminate; auto.
  - intros [G' [H [WF' MT EQ [e [l [r [EQT AN]]]]]]]. exists l, r.
    apply Pattern_When_correct. split; trivial.
    apply Pattern_Branch_correct; trivial. exists G'. repeat split; trivial.
    now exists e. unfold fixed_branch. rewrite EQT. destruct AN as [AN|AN]; now rewrite AN.
Qed.