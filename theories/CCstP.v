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

Definition CCstP {S} (P:Pat S) f := (Branch P) when (fun '(B,_,_,_) => fixed_branch f B).