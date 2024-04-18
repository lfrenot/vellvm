From Vellvm Require Import Syntax Tactics.
(* From ITree Require Import ITree Eq. *)
From Pattern Require Import Base Head Focus Patterns.
(* Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
(* Import ListNotations. *)
(* Import Map MapF MapF.P MapF.P.F. *)
Import gmap Head Focus Patterns.

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

Definition CCstP_f {S} f: (bid * blk * S → bool) := fun '(_, b, _) => fixed_branch f b.

Definition CCstP {S} f (P:Pattern S) := (Branch P) when (CCstP_f f).

Record CCstP_sem f id (B: blk) (G G': ocfg) := {
  EQ: G' = delete id G;
  IN: G !! id = Some B;
  AN: exists e l r, B.(blk_term) = TERM_Br e l r /\ (f e = Zero \/ f e = One)
}.

Lemma Pattern_CCstP_correct {S}: forall f G id B P (X:S), 
    (id, B, X) ∈ (MatchAll (CCstP f P) G) <->
    exists G', X ∈ (MatchAll P G') /\ CCstP_sem f id B G G'.
Proof.
  intros *. unfold CCstP, CCstP_f, fixed_branch. rewrite Pattern_When_correct, Pattern_Branch_correct.
  split.
  - intros [AN (G' & [EQ (e & l & r & BR) IN] & INX)].
    exists G'. split; trivial. split; trivial.
    exists e, l, r. split; trivial.
    break_match_hyp; try discriminate. inversion BR. subst. break_match_hyp; auto; discriminate.
  - intros (G' & INX & [EQ IN (e & l & r & BR & AN)]).
    split. rewrite BR. destruct AN; break_match_goal; auto; discriminate.
    exists G'. repeat split; trivial.
    now exists e, l ,r.
Qed.