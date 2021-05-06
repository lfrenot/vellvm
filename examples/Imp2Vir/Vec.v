From Coq Require Import
     Lia
     Lists.List
     Arith
     ZArith.

From Vellvm Require Import
     Syntax.

From tutorial Require Import Fin.

Section Vec.

Open Scope nat_scope.

Definition t (A : Type) (n : nat) : Type := { l : list A | length l = n }.

Notation vec' l := (exist (fun l' : list _ => _) l _).

Theorem vector_proj1_unique : forall A n (v v' : t A n),
    proj1_sig v = proj1_sig v' -> v = v'.
Proof.
  intros.
  destruct v, v'.
  simpl in *.
  destruct H.
  f_equal.
  subst. rewrite Eqdep_dec.UIP_refl_nat.
  reflexivity.
Qed.

Theorem vector_length : forall A n (v : t A n),
  length (proj1_sig v) = n.
Proof.
  destruct v.
  simpl.
  exact e.
Qed.

Program Definition cast {A} {n n'} (v : t A n) (H : n = n') : t A n' :=
  exist _ (proj1_sig v) _.
Next Obligation.
  apply vector_length.
Defined.

Program Definition empty (A : Type) : t A 0 := vec' nil.

Program Definition cons {A} {n} h (v : t A n) : t A (S n) := vec' (h::v).
Next Obligation.
  destruct v. simpl in *.
  f_equal.
  assumption.
Defined.

Program Definition hd {A} {n} (v : t A (S n)) : A :=
  match proj1_sig v with
  | h :: _ => h
  | nil => _
  end.
Next Obligation.
  destruct v.
  destruct x.
  - discriminate e.
  - exact a.
Qed.

Program Definition tl {A} {n} (v : t A (S n)) : t A n :=
  match proj1_sig v with
  | _ :: v' => vec' v'
  | nil => _
  end.
Next Obligation.
  destruct v.
  simpl in *. subst. simpl in e. injection e as e. exact e.
Defined.
Next Obligation.
  destruct v.
  destruct x.
  - discriminate e.
  - simpl in *. discriminate Heq_anonymous.
Qed.

Program Definition nth {A} {n} (v : t A n) (i : fin n) : A :=
  match proj1_sig v with
  | h :: l => List.nth i v h
  | nil => _
  end.
Next Obligation.
  destruct n. destruct i.
  - lia.
  - destruct v. simpl in *. subst. discriminate e.
Qed.

Theorem nth_destruct : forall A n (v : t A n) i a, nth v i = List.nth (proj1_sig i) (proj1_sig v) a.
Proof.
  intros ? ? [] [] ?.
  subst.
  simpl.
  unfold nth. simpl. destruct x eqn:?.
  - simpl in l. lia.
  - subst. rewrite (nth_indep _ a a0 l). reflexivity.
Qed.

Theorem nth_rewrite_error : forall A n (v : t A n) i, List.nth_error (proj1_sig v) (proj1_sig i) = Some (nth v i).
Proof.
  intros ? ? [] [].
  erewrite nth_destruct.
  simpl in *.
  apply nth_error_nth'.
  lia.
  Unshelve. destruct x ; [ simpl in * ; lia | assumption ].
Qed.

Theorem nth_destruct_error : forall A n (v : t A n) i a, nth v i = a <-> List.nth_error (proj1_sig v) (proj1_sig i) = Some a.
Proof.
  intros ? ? [] [] ?.
  split ; intro ; subst ; simpl.
  - rewrite <- nth_rewrite_error. simpl. reflexivity.
  - rewrite nth_rewrite_error in H. inversion H. reflexivity.
Qed.

Theorem nth_destruct_eq : forall A n n' (v : t A n) (v' : t A n') i i', nth v i = nth v' i' <-> List.nth_error (proj1_sig v) (proj1_sig i) = List.nth_error (proj1_sig v') (proj1_sig i').
Proof.
  split ; intros ; subst ; simpl.
  - rewrite 2 nth_rewrite_error.
    f_equal. assumption.
  - rewrite 2 nth_rewrite_error in H.
    inversion H.
    reflexivity.
Qed.

Program Definition append {A} {n n'} (v : t A n) (v' : t A n') :
  t A (n + n') := vec' ((proj1_sig v) ++ proj1_sig v').
Next Obligation.
  rewrite app_length. destruct v, v'. simpl. subst. reflexivity.
Defined.

Definition In {A} {n} a (v : t A n) := List.In a (proj1_sig v).

Theorem vector_in_app_iff : forall A n n' (v : t A n) (v' : t A n') (a : A),
  In a (append v v') <-> In a v \/ In a v'.
Proof.
  intros ? ? ? [] [] ?.
  unfold In in *. simpl in *.
  apply in_app_iff.
Qed.

Theorem vector_app_nth1 :
  forall A n n' (v : t A n) (v' : t A n') (k : fin n), nth (append v v') (L n' k) = nth v k.
Proof.
  intros.
  apply nth_destruct_eq.
  destruct v, v', k.
  simpl in *.
  apply nth_error_app1.
  lia.
Qed.

Theorem vector_app_nth2 :
  forall A n n' (v : t A n) (v' : t A n') (k : fin n'), nth (append v v') (R n k) = nth v' k.
Proof.
  intros.
  apply nth_destruct_eq.
  destruct v, v', k.
  simpl in *.
  replace x1 with (n + x1 - length x) at 2 by lia.
  apply nth_error_app2.
  lia.
Qed.

Theorem In_nth :
  forall A n (v : t A n) (x : A), In x v -> exists n : fin n, nth v n = x.
Proof.
  intros.
  eapply In_nth_error in H.
  destruct H as [ n0 H ].
  eexists (fi' n0).
  eapply nth_destruct_error.
  exact H.
  Unshelve. apply Util.nth_error_in in H. rewrite <- vector_length with (v := v). assumption.
Qed.

Program Definition splitat {A} i {j} (v : t A (i+j)) :
  t A i * t A j :=
  (vec' (firstn i (proj1_sig v)), vec' (skipn i (proj1_sig v))).
Next Obligation.
  destruct v. simpl in *. rewrite firstn_length. rewrite e.
  rewrite (plus_n_O i) at 1. rewrite Nat.add_min_distr_l. rewrite Nat.min_0_l.
  apply Nat.add_0_r.
Defined.
Next Obligation.
  destruct v. simpl in *. rewrite skipn_length. apply Nat.add_sub_eq_l. auto.
Defined.

Program Definition splitat' {A} {k} (i : fin k) (v : t A k) :
  t A i * t A (k-i) :=
  splitat i (cast v _).
Next Obligation.
  destruct i. simpl. lia.
Defined.

Theorem splitat_append : forall A n n' (v : t A n) (v' : t A n'),
  splitat n (append v v') = (v,v').
Proof.
  unfold splitat, append.
  destruct v, v'.
  simpl.
  subst.
  f_equal ; apply vector_proj1_unique ; simpl.
  - rewrite firstn_app.
    rewrite firstn_all.
    rewrite Nat.sub_diag.
    rewrite app_nil_r.
    reflexivity.
  - rewrite skipn_app.
    rewrite skipn_all.
    rewrite Nat.sub_diag.
    reflexivity.
Qed.

Theorem append_splitat : forall A n n' (v : t A n) (v' : t A n') (v'' : t A (n+n')),
  splitat n v'' = (v, v') -> v'' = append v v'.
Proof.
  intros.
  destruct v, v', v''.
  unfold splitat, append in *.
  simpl in *.
  injection H as ?.
  subst x x0.
  apply vector_proj1_unique. simpl.
  rewrite (firstn_skipn n x1).
  reflexivity.
Qed.

Program Definition uncons {A} {n} (v : t A (S n)) : A * t A n :=
  match proj1_sig v with
  | a :: t => (a, vec' t)
  | _ => _
  end.
Next Obligation.
  destruct v as [[] ?].
  discriminate e.
  simpl in *.
  injection Heq_anonymous as ?.
  subst.
  auto.
Defined.
Next Obligation.
  destruct v as [[] ?].
  discriminate e.
  simpl in *. injection e as ?.
  refine (a, vec' l). exact H0.
Defined.

Theorem uncons_cons : forall A n (v : t A n) a, uncons (cons a v) = (a, v).
Proof.
  intros.
  unfold uncons.
  simpl.
  f_equal.
  apply vector_proj1_unique.
  simpl.
  reflexivity.
Qed.

Theorem cons_uncons : forall A n (v : t A (S n)) (v' : t A n) a, uncons v = (a, v') -> v = cons a v'.
Proof.
  intros.
  destruct v, v'.
  unfold uncons in H.
  destruct x.
  - simpl in e. lia.
  - simpl in *.
    unfold cons.
    simpl.
    inversion H.
    subst.
    apply vector_proj1_unique.
    reflexivity.
Qed.

Program Definition rev {A} {n} (v : t A n) : t A n :=
  vec' (rev (proj1_sig v)).
Next Obligation.
  destruct v.
  rewrite rev_length.
  auto.
Defined.

Program Definition seq (start len : nat) : t nat len :=
  vec' (seq start len).
Next Obligation.
  rewrite seq_length.
  reflexivity.
Defined.

Program Definition map {A B} {n} (f : A -> B) (v : t A n) : t B n :=
  vec' (map f (proj1_sig v)).
Next Obligation.
  destruct v.
  rewrite map_length.
  auto.
Defined.

End Vec.

Ltac split_vec v n1 :=
  let vp := fresh "vp" in
  let v1 := fresh v "1" in
  let v2 := fresh v "2" in
  remember (splitat n1 v) as vp eqn:?Heqvp;
  destruct vp as [ v1 v2 ] eqn:?Heq;
  subst vp;
  symmetry in Heqvp;
  apply append_splitat in Heqvp;
  subst v.

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.
Notation "h :: t" := (cons h t) (at level 60, right associativity).
Infix "++" := append : vec_scope.
Notation vec' l := (exist (fun l' : list _ => _) l _).