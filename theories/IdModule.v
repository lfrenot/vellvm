(** This file contructs an ordered type from [block_id].
    This allows to make a FMap that uses them as keys. *)

From Vellvm Require Import Syntax ScopeTheory.
From QuickChick Require Import StringOT.
From Coq Require Import OrderedType Strings.String ZArith Lia.

Module IdOT <: OrderedType.

(** The type for FMap's keys needs to be named t. *)
Definition t := block_id.

(** The equality on [block_id]. FMap needs [eq] to be a definition. *)
Variant eq': t -> t -> Prop :=
  | EqName s s' : s = s' -> eq' (Name s) (Name s')
  | EqAnon n n' : n = n' -> eq' (Anon n) (Anon n')
  | EqRaw n n' : n = n' -> eq' (Raw n) (Raw n')
.

Definition eq := eq'.

(** Proofs that [eq] is an equivalence. *)
#[local] Hint Constructors eq' : core.
#[local] Hint Unfold eq: core.

Theorem eq_refl: forall x:t, eq x x.
Proof.
    induction x; cbn; auto.
Qed.

Theorem eq_sym : forall x y : t, eq x y -> eq y x.
Proof. 
    intros ? ? H. inversion H; auto.
Qed.

Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
    intros ? ? ? H1 H2. inversion H1; inversion H2; subst; auto.
Qed.


(** Makes [eq] an Equivalence. Allows using the transitivity, reflexivity and symmetry tactics. *)
#[global] Instance r_eq: Equivalence eq.
Proof.
  constructor; red.
  apply eq_refl.
  apply eq_sym.
  apply eq_trans.
Qed.

#[global] Instance r_eq': Equivalence eq'.
Proof.
  constructor; red.
  apply eq_refl.
  apply eq_sym.
  apply eq_trans.
Qed.

(** Allows using the symmetry tactic for [~eq]. *)
#[global] Instance s_neq: Symmetric (fun x y => ~eq x y).
Proof.
  intros ? ? H Abs. apply H. now symmetry.
Qed.

(** Decidability, Equality and boolean version. *)
Theorem eq_dec: forall x y: t, { eq x y } + { ~ eq x y }.
Proof.
  induction x,y; cbn; try (right; intro Abs; now inversion Abs).
  2, 3: case (Z.eq_dec n n0); [intros ->; left; auto|]; intro H; right; intro Abs; inversion Abs; auto.
  case (string_dec s s0). intros ->. left. auto. intro H. right. intro Abs. inversion Abs. auto.
Qed.

Theorem eq_eq: forall x y: t, eq x y <-> x=y.
Proof.
  split. intros []; subst; auto. intros ->. reflexivity.
Qed.

Definition eqb (b b':t) :=
  match b,b' with
  | Name s, Name s' => String.eqb s s'
  | Anon n, Anon n' => Z.eqb n n'
  | Raw n, Raw n' => Z.eqb n n'
  | _ , _ => false
  end.

Lemma eqb_eq : forall b b':t, eqb b b' = true <-> b=b'.
Proof.
  intros.
  split.
  - destruct b,b' ;
      try (intros ; simpl in H ; discriminate) ;
      simpl ; intros ; f_equal ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
  - intros ; subst.
    destruct b' ; simpl ;
      try (now apply String.eqb_eq) ;
      try (now apply Z.eqb_eq).
Qed.

(** Strict order on [block_id]. Arbitrarily, Name < Anon < Raw. *)
Variant lt': t -> t -> Prop :=
  | LtName s s' : StringOT.lt s s' -> lt' (Name s) (Name s')
  | LtAnon n n' : Z.lt n n' -> lt' (Anon n) (Anon n')
  | LtRaw n n' : Z.lt n n' -> lt' (Raw n) (Raw n')
  | LtNameAnon s n: lt' (Name s) (Anon n)
  | LtNameRaw s n: lt' (Name s) (Raw n)
  | LtAnonRaw n n': lt' (Anon n) (Raw n')
.

Definition lt := lt'.

#[local] Hint Constructors lt' : core.
#[local] Hint Unfold lt: core.

Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
  intros ? ? ? H1 H2. inversion H1; inversion H2;subst; auto; (try now inversion H2); inversion H5; subst; constructor.
  - eapply StringOT.lt_trans. apply H. trivial.
  - lia.
  - lia.
Qed.

Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
  intros x y H Abs. inversion Abs; subst; inversion H; subst.
  - eapply StringOT.lt_not_eq. apply H2. reflexivity.
  - lia.
  - lia.
Qed.

Theorem compare : forall x y : t, Compare lt eq x y.
Proof.
  induction x, y; try (apply GT; now auto); try (apply LT; now auto).
  - assert (H: Compare StringOT.lt StringOT.eq s s0) by apply StringOT.compare.
    inversion H. apply LT. auto. apply EQ. auto. apply GT. auto.
  - case (Z_dec' n n0). intro s. case s.
    * intro. apply LT. auto.
    * intro. apply GT. auto.
    * intro. apply EQ. auto.
  - case (Z_dec' n n0). intro s. case s.
    * intro. apply LT. auto.
    * intro. apply GT. auto.
    * intro. apply EQ. auto.
Qed.

End IdOT.