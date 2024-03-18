From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule MapCFG Head Focus Patterns.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Patterns.

(* Print texp.
Print exp.
Search exp. *)

Notation exp := (texp dtyp).

Definition IsTrue: exp -> Prop. Admitted.

Definition eqb_exp : exp -> exp -> bool. Admitted.

Lemma eqb_exp_eq : forall e e', eqb_exp e e' = true -> IsTrue e -> IsTrue e'. Admitted.

Definition is_branch_using e (b: blk) := match b.(blk_term) with
    | TERM_Br e' _ _ => eqb_exp e e'
    | _ => false
end.

Definition CCstP {S} (P:Pat S) e := (Block P) when (fun '(B, _) => is_branch_using e B).

