From Vellvm Require Import Syntax ScopeTheory.
From QuickChick Require Import StringOT.
From Coq Require Import OrderedType Strings.String ZArith Lia.

Module IdOT <: OrderedType.

Definition t := block_id.

Definition eq b b': Prop :=
    match b,b' with
      | Name s, Name s' => @Logic.eq string s s'
      | Anon n, Anon n' => @Logic.eq int n n'
      | Raw n, Raw n' => @Logic.eq int n n'
      | _ , _ => False
  end.

Theorem eq_refl: forall x:t, eq x x.
Proof.
    induction x; cbn; trivial.
Qed.

Theorem eq_sym : forall x y : t, eq x y -> eq y x.
Proof. 
    induction x, y; cbn; intro H; now destruct H.
Qed.

Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
    induction x,y,z; cbn; intros H H'; now destruct H, H'.
Qed.

Theorem eq_dec: forall x y: t, { eq x y } + { ~ eq x y }.
Proof.
  induction x,y; cbn; auto.
  apply string_dec. apply Z.eq_dec. apply Z.eq_dec.
Qed.

Definition lt b b': Prop :=
  match b, b' with
    | Name s, Name s' => StringOT.lt s s'
    | Name s, _ => True
    | Anon n, Anon n' => Z.lt n n'
    | Anon _, Name _ => False
    | Anon _, _ => True
    | Raw n, Raw n' => Z.lt n n'
    | Raw _, _ => False
  end.

Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof.
  induction x,y,z; cbn; try contradiction; auto.
  apply StringOT.lt_trans. lia. lia.
Qed.

Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
  induction x, y; cbn; try contradiction; auto.
  apply StringOT.lt_not_eq. lia. lia.
Qed.

Theorem compare : forall x y : t, Compare lt eq x y.
Proof.
  unfold lt, eq. induction x,y.
  - assert (H: Compare StringOT.lt StringOT.eq s s0) by apply StringOT.compare.
    destruct H. now apply LT. now apply EQ. now apply GT.
  - now apply LT.
  - now apply LT.
  - now apply GT.
  - case (Z_dec' n n0). intro s. case s.
    * intro. now apply LT.
    * intro. now apply GT.
    * intro. now apply EQ.
  - now apply LT.
  - now apply GT.
  - now apply GT.
  - case (Z_dec' n n0). intro s. case s.
    * intro. now apply LT.
    * intro. now apply GT.
    * intro. now apply EQ.
Qed.

End IdOT.

Print IdOT.