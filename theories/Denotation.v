(** This file contains the tools to prove the correctness of the block fusion optimization.
    It relies on the garantees given by the [BlockFusion] pattern. *)

From Vellvm Require Import Syntax ScopeTheory Semantics Theory Tactics Denotation DenotationTheory.
From ITree Require Import ITree Eq HeterogeneousRelations.
From Pattern Require Import Base Patterns BlockFusion.
(* Require Import FSets.FMapAVL FSets.FMapFacts. *)
Require Import List.
(* Import TopLevelBigIntptr InterpretationStack. *)
(* Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Patterns. *)
From stdpp Require Import prelude.
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
  blk_phis       := A.(blk_phis);
  blk_code       := fusion_code A B;
  blk_term       := B.(blk_term);
  blk_comments   := fusion_comments A B
|}.

(* Import SemNotations. *)
(* todo better representation*)
Definition bk_renaming := bid -> bid.
From stdpp Require Import prelude fin_maps.

Definition exps_rename σ (id: bid) e (φ: gmap bid (exp dtyp)) := {[σ id := e]} ∪ φ.

Definition phi_rename (σ : bk_renaming) (ϕ:  phi dtyp): phi dtyp :=
  match ϕ with
    | Phi τ exps => Phi τ (map_fold (exps_rename σ) ∅ exps)
  end.

Definition bk_phi_rename (σ : bk_renaming) (b: blk): blk := {|
  blk_phis       := List.map (fun '(x,φ) => (x,phi_rename σ φ)) b.(blk_phis);
  blk_code       := b.(blk_code);
  blk_term       := b.(blk_term);
  blk_comments   := b.(blk_comments)
|}.

Definition ocfg_rename (σ : bk_renaming) (g: ocfg): ocfg := fmap (bk_phi_rename σ) g.

Record dom_renaming (σ : bk_renaming) (from to : list bid) : Prop :=
  {
    in_dom : forall id, List.In id from -> List.In (σ id) to;
    out_dom : forall id, ~ List.In id from -> (σ id) = id
  }.

(* Nodes that may exit the graph *)

Definition outgoing_bks (g : ocfg) : gset bid :=
  set_fold (fun id acc => predecessors id g ∪ acc) ∅ (outputs g).

(* inputs g. *)

Module Type DenotationTheory (LP : LLVMParams.LLVMParams).
  Module D := Denotation LP.
  Import D.
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

  (* Ltac solve_find_block := *)
  (*   cbn; *)
  (*   match goal with *)
  (*   (* If the [ocfg] contains a single block, we are done exactly if it has the id we are looking for *) *)
  (*   | |- find_block [_] _ = _ => apply find_block_eq; reflexivity *)
  (*   (* Otherwise, if the [ocfg] has a head block, we: *) *)
  (*   (*      - first check if that's the one we are looking for *) *)
  (*   (*      - otherwise dismiss it, focus our well-formedness hypothesis similarly, and continue recursively. *) *)
  (*   (*      - if it is instead built by appending two sub-graphs, we call ourselves recursively in each branch, *) *)
  (*   (*      and don't forget to shape the well-formedness hypothesis in each case beforehand. *) *)
  (*   (*    *) *)
  (*   | h: wf_ocfg_bid _ |- find_block (_ :: _) _ = _ => *)
  (*       first [apply find_block_eq; reflexivity | *)
  (*               apply find_block_tail_wf; [eassumption | apply wf_ocfg_bid_cons in h; solve_find_block]] *)
  (*   | h: wf_ocfg_bid _ |- find_block (_ ++ _) _ = _ => *)
  (*       first [apply find_block_app_l_wf; [eassumption | apply wf_ocfg_bid_app_l in h; solve_find_block] | *)
  (*               apply find_block_app_r_wf; [eassumption | apply wf_ocfg_bid_app_r in h; solve_find_block]] *)
  (*   end. *)

  (* Ltac vjmp := *)
  (*   rewrite denote_ocfg_unfold_in; cycle 1; *)
  (*   [match goal with *)
  (*    | h: hidden_cfg _ |- _ => inv h *)
  (*    | h: visible_cfg _ |- _ => inv h *)
  (*    | _ => idtac *)
  (*    end; *)
  (*    cbn; rewrite ?convert_typ_ocfg_app; *)
  (*    try solve_find_block |]. *)

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
From Paco Require Import paco.

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

(* Transparent denote_block. *)
(* Print denote_ocfg. *)

Definition post_ocfg (g1 : ocfg) (σ : bid -> bid) : relation (bid * bid + uvalue) :=
  sum_rel (fun '(f,t) '(f',t') =>
             t ∈ (inputs g1) /\
               t' = t /\
               f' = σ f) Logic.eq.

Definition denote_ocfg_equiv_cond (g1 g2 g2': ocfg) (TO :list bid) (σ: bid -> bid) :=
  forall origin header,
    header ∈ TO ->
    eutt (post_ocfg g1 σ)
      (⟦g2 ⟧bs (origin, header))
      (⟦g2'⟧bs (σ origin, header)).

(* Definition denote_ocfg_equiv_cond (g1 g2 g2': ocfg) TO σ := *)
(*   forall origin header, *)
(*     header ∈ TO -> *)
(*       (exists x, ⟦g2 ⟧bs (origin, header) = Ret (inr x) /\ *)
(*             ⟦g2'⟧bs (origin, header) = Ret (inr x)) *)
(*     \/ *)
(*       (exists from to, to ∈ (inputs g1) /\ *)
(*                   ⟦g2⟧bs (origin, header) = Ret (inl (from, to)) /\ *)
(*                   ⟦g2'⟧bs (origin, header) = Ret (inl (σ from, to))) *)
(* . *)

(*
   x = φ(l1,e1)(l2,e2)
   y = φ(l3,e3)(l4,e4)
   ...
 *)
Lemma denote_phis_cons : forall b φ φs,
                 ⟦φ :: φs⟧Φs b ≈
                 (v <- ⟦φ⟧Φ b;
                 ⟦φs⟧Φs b;;
                 Subevent.trigger (LocalWrite (fst v) (snd v)))%monad
.
Proof.
Admitted.

(*

block fusion: je sortais par b, je sors maintenant par a

σ b = a

σ : renaming map
- domain: predecessors of (outputs g2) renamed
          into (inputs of g2') (⊆ (inputs of g2))

ici: σ sur le phi node peut renommer les labels en jeu,
     mais si oui ne peut pas le renommer en un autre label en jeu.

dom

 *)

Definition dom_phi (φ: phi dtyp) : gset bid :=
  match φ with
  | Phi _ l => dom l
  end.

(* Record σφSafe (σ: bid -> bid) (φ: phi dtyp) : Prop := {
  σφSafe1: forall id id' e e',
    match φ with |Phi _ l =>
      (id, e) ∈ l -> (id', e') ∈ l -> σ id = σ id' -> e = e'
    end;
  σφSafe2: forall id id', id <> id' -> σ id = σ id' -> id ∈ (dom_phi φ) -> ~ id' ∈ (dom_phi φ)
}. *)
   (* ~ id ∈ (dom_phi φ) -> ~ σ id ∈ (dom_phi (phi_rename σ φ)); *)
  (* σφSafe_norepet: Coqlib.list_norepet (dom_phi φ) *)
   (* forall id, id ∈ (dom_phi φ) -> σ id = id \/ ~ (σ id ∈ (dom_phi φ)) *)


(* Definition σφSafe (σ: bid -> bid) (φ: phi dtyp) : Prop := forall id id' e e', match φ with |Phi _ l =>
  (id, e) ∈ l -> (id', e') ∈ l -> σ id = σ id' -> e = e'
end. *)

Record σφSafe (σ : bid -> bid) (φ : phi dtyp) (from : bid) := {
    EQ: forall id id' e e',
      match φ with
      |Phi _ l => l !! id = Some e -> l !! id' = Some e' -> σ id = σ id' -> e = e'
      end;
    IN: σ from ∈ (dom_phi (phi_rename σ φ)) -> from ∈ (dom_phi φ)
  }.
(* σ from ∈ (dom_phi (phi_rename σ φ)) -> from ∈ (dom_phi φ). *)

Lemma dom_phi_cons :
  forall φ τ id id' e,
    id ∈ (dom_phi (Phi τ φ)) ->
    id ∈ (dom_phi (Phi τ ({[id' := e]} ∪ φ))).
Proof.
  intros *. unfold dom_phi. set_solver.
Qed.

Lemma dom_phi_cons2: forall φ τ id id' e, id <> id' -> id ∈ (dom_phi (Phi τ ({[id' := e]} ∪ φ))) -> id ∈ (dom_phi (Phi τ φ)).
Proof.
  intros * NEQ. unfold dom_phi. set_solver.
Qed.

Definition phi_rename_union_P φ := forall σ b τ id a, b ∈ dom_phi (phi_rename σ (Phi τ φ)) -> b ∈ dom_phi (phi_rename σ (Phi τ (<[id:=a]>φ))).

Lemma phi_rename_union: forall φ,
  phi_rename_union_P φ.
Proof.
  intros ?. apply map_ind; unfold phi_rename_union_P. intros *. cbn. rewrite map_fold_empty. set_solver.
  intros * NIN IH * IN. cbn in *. rewrite map_fold_insert; auto.
Admitted.

(* Lemma phi_rename_union (σ: bk_renaming) (e1 e2: gmap bid (exp dtyp)): kmap σ (e1 ∪ e2) = (kmap σ e1 ∪ kmap σ e2).
Proof.
  intros. *)

(*

Lemma kmap_dom: ∀ {K : Type} {M : Type → Type} {D : Type} {H : ∀ A : Type, Dom (M A) D} {H0 : FMap M} {H1 : ∀ A : Type, Lookup K A (M A)} {H2 : ∀ A : Type, Empty (M A)} {H3 : ∀ A : Type, PartialAlter K A (M A)} {H4 : OMap M} {H5 : Merge M} {H6 : ∀ A : Type, MapFold K A (M A)} {EqDecision0 : EqDecision K} {H7 : ElemOf K D} {H8 : Empty D} {H9 : Singleton K D} {H10 : Union D} {H11 : Intersection D} {H12 : Difference D}, FinMapDom K M D → ∀ {Elements0 : Elements K D}, FinSet K D → ∀ {K2 : Type} {M2 : Type → Type} {D2 : Type} {H14 : ∀ A : Type, Dom (M2 A) D2} {H15 : FMap M2} {H16 : ∀ A : Type, Lookup K2 A (M2 A)} {H17 : ∀ A : Type, Empty (M2 A)} {H18 : ∀ A : Type, PartialAlter K2 A (M2 A)} {H19 : OMap M2} {H20 : Merge M2} {H21 : ∀ A : Type, MapFold K2 A (M2 A)} {EqDecision1 : EqDecision K2} {H22 : ElemOf K2 D2} {H23 : Empty D2} {H24 : Singleton K2 D2} {H25 : Union D2} {H26 : Intersection D2} {H27 : Difference D2}, FinMapDom K2 M2 D2 → ∀ {A : Type} (f : K → K2), ∀ m : M A, dom (kmap f m) ≡ set_map f (dom m).
*) 

(* Lemma p_eq : PreOrder eq. *)

Lemma eq_dec_bid: forall (id id': bid), {id=id'} + {id<>id'}. Admitted.

Lemma σφSafe_cons:
  forall σ (τ:dtyp) φ (id:bid) e b,
    b <> id ->
    φ !! id = None ->
    σφSafe σ (Phi τ (<[id := e]> φ)) b ->
    σφSafe σ (Phi τ φ) b.
Proof.
  intros * NEQ LUN [SAFE1 SAFE2]. split.
  - intros * IN IN' EQ. eapply SAFE1. 3: apply EQ.
    all: by simplify_map_eq.
  - intros IN.
    forward SAFE2.
    + unfold dom_phi, phi_rename in IN |- *. rewrite map_fold_insert.
      -- set_solver.
      -- constructor; auto. intros ? * ? ?. now subst.
      -- intros * ? * ?. now subst.
      -- unfold exps_rename. intros j1 j2 * NEQj M1 M2.
         pose proof eq_dec_bid (σ j1) (σ j2) as [EQ|nEQ].
         (* destruct DEC. *)
         ** pose proof SAFE1 _ _ _ _ M1 M2 EQ as EQz. now rewrite EQ, EQz.
         ** rewrite <- !insert_union_singleton_l. now apply insert_commute.
      -- trivial.
      (* rewrite elem_of_dom in IN |- *. destruct IN as [x IN].
      exists x. Search map_fold (_!!_).
      cbn in *. 
      unfold kmap. unfold map_to_list. admit. *)
    + unfold dom_phi in *. cbn in *. set_solver.
    (* unfold dom_phi in *. *)
    (* do 2 case_match. *)
    (* intros ?. *)
    (* apply SAFE2. now apply dom_phi_cons. trivial. *)
Qed.

(*
Lemma assoc_in: forall (b:bid) (e: exp dtyp) (φ : list (bid * exp dtyp)), Util.assoc b φ = Some e -> (b, e) ∈ φ.
Proof.
  intros *. induction φ as [|(b', e') φ IH]; intro H.
  - inversion H.
  - inversion H. break_match_hyp.
    * inversion H1. rewrite RelDec.rel_dec_correct in Heqb0; subst. now left.
    * right. now apply IH.
Qed.

Lemma assoc_nin: forall (b: bid) (φ: list (bid * exp dtyp)), Util.assoc b φ = None -> forall e, ~ (b, e) ∈ φ.
Proof.
  intros. induction φ as [|(b', e') φ IH]. auto.
  inversion H. break_match_hyp. discriminate.
  apply RelDec.neg_rel_dec_correct in Heqb0.
  intros [EQ|IN]. apply pair_equal_spec in EQ as []. auto.
  now apply IH.
Qed.

*)



(* Lemma σφSafe_rename: forall σ τ i x m b, σφSafe σ (Phi τ (<[i:=x]> m)) b -> m !! i = None ->
  <[i:=x]> m !! b = map_fold (exps_rename σ) ∅ (<[i:=x]> m) !! σ b.
Proof.
  intros * [SAFE1 SAFE2] NIN. cbn in *. unfold exps_rename in *.
  rewrite map_fold_insert.
  - pose proof eq_dec_bid b i as [EQ|NEQ]. 2: pose proof eq_dec_bid (σ b) (σ i) as [EQσ|NEQσ].
    * subst. rewrite lookup_union. rewrite lookup_singleton. rewrite union_Some_l. apply lookup_insert.
    * forward SAFE2. {
        rewrite EQσ. rewrite map_fold_insert. set_solver.
        - constructor; auto. intros ? * ? ?. now subst.
        - intros * ? * ?. now subst.
        - intros * NEQ' M1 M2. pose proof eq_dec_bid (σ j1) (σ j2) as [EQj|NEQj].
          * pose proof SAFE1 _ _ _ _ M1 M2 EQj as EQz. now rewrite EQj, EQz.
          * rewrite <- !insert_union_singleton_l. now apply insert_commute.
        - trivial.
      } 
      rewrite lookup_union. rewrite EQσ. rewrite lookup_singleton. rewrite union_Some_l.
      apply elem_of_dom in SAFE2 as [y SAFE2]. rewrite SAFE2.
      assert (x=y). eapply SAFE1. apply lookup_insert. apply SAFE2. auto. now subst.
    *  
      
  - constructor; auto. intros ? * ? ?. now subst.
  - intros * ? * ?. now subst.
  - intros * NEQ M1 M2. pose proof eq_dec_bid (σ j1) (σ j2) as [EQj|NEQj].
      * pose proof SAFE1 _ _ _ _ M1 M2 EQj as EQz. now rewrite EQj, EQz.
      * rewrite <- !insert_union_singleton_l. now apply insert_commute.
  - trivial.
  
  pose proof eq_dec_bid b i as [EQ|NEQ].
  - subst. rewrite map_fold_insert.
    * unfold exps_rename. rewrite lookup_union. rewrite lookup_singleton. rewrite union_Some_l. apply lookup_insert.
    * constructor; auto. intros ? * ? ?. now subst.
    * intros * ? * ?. now subst.
    * admit.
    * trivial.
  - rewrite map_fold_insert.
    *  *)

Definition phi_rename_correct_P φ := forall τ σ b, σφSafe σ (Phi τ φ) b -> φ !! b = (map_fold (exps_rename σ) ∅ φ) !! σ b.

Lemma phi_rename_correct: forall φ, phi_rename_correct_P φ.
Proof.
  intros. apply map_ind; unfold phi_rename_correct_P.
  - reflexivity.
  - intros * NIN REC * [SAFE1 SAFE2]. cbn in *. unfold exps_rename in *.
    rewrite map_fold_insert.
    * pose proof eq_dec_bid b i as [EQ|NEQ]. 2: pose proof eq_dec_bid (σ b) (σ i) as [EQσ|NEQσ].
      + subst. rewrite lookup_union. rewrite lookup_singleton. rewrite union_Some_l. apply lookup_insert.
      + forward SAFE2. {
          rewrite EQσ. rewrite map_fold_insert. set_solver.
          - constructor; auto. intros ? * ? ?. now subst.
          - intros * ? * ?. now subst.
          - intros * NEQ' M1 M2. pose proof eq_dec_bid (σ j1) (σ j2) as [EQj|NEQj].
            * pose proof SAFE1 _ _ _ _ M1 M2 EQj as EQz. now rewrite EQj, EQz.
            * rewrite <- !insert_union_singleton_l. now apply insert_commute.
          - trivial.
        } 
        rewrite lookup_union. rewrite EQσ. rewrite lookup_singleton. rewrite union_Some_l.
        apply elem_of_dom in SAFE2 as [y SAFE2]. rewrite SAFE2.
        assert (x=y). eapply SAFE1. apply lookup_insert. apply SAFE2. auto. now subst.
      + rewrite lookup_union. rewrite <- REC with (τ:=τ).
        now simplify_map_eq. eapply σφSafe_cons. apply NEQ. trivial. split. apply SAFE1. apply SAFE2.
    * constructor; auto. intros ? * ? ?. now subst.
    * intros * ? * ?. now subst.
    * intros * NEQ M1 M2. pose proof eq_dec_bid (σ j1) (σ j2) as [EQj|NEQj].
        + pose proof SAFE1 _ _ _ _ M1 M2 EQj as EQz. now rewrite EQj, EQz.
        + rewrite <- !insert_union_singleton_l. now apply insert_commute.
    * trivial.
Qed.

Definition denote_phi_rename_P φ := forall τ σ b, σφSafe σ (Phi τ φ) b -> ∀ x, ⟦ (x, (Phi τ φ)) ⟧Φ b ≈ ⟦ (x, phi_rename σ (Phi τ φ)) ⟧Φ (σ b).

Lemma denote_phi_rename_aux: forall φ, denote_phi_rename_P φ.
Proof.
  intros. apply map_ind; unfold denote_phi_rename_P.
  - reflexivity.
  - cbn.
    match goal with
      |- context[raise ?s] => generalize s
    end.
    intros * NIN REC * SAFE *.
    pose proof phi_rename_correct _ _ _ _ SAFE as EQ. now rewrite EQ.
Qed.

Lemma denote_phi_rename: forall φ σ b, σφSafe σ φ b -> ∀ x, ⟦ (x, φ) ⟧Φ b ≈ ⟦ (x, phi_rename σ φ) ⟧Φ (σ b).
Proof.
  intros [x φ]. apply denote_phi_rename_aux.
Qed.

Definition σφsSafe σ (φs : list (local_id * phi dtyp)) from : Prop :=
  List.Forall (fun '(_,φ) => σφSafe σ φ from) φs.

(* Definition σφsfSafe σ (φs : list (local_id * phi dtyp)) from: Prop :=
  List.Forall (fun '(_,φ) => σφfSafe σ φ from) φs. *)

Lemma denote_phis_rename
  φs σ from
  (HSafe: σφsSafe σ φs from):
  ⟦ φs ⟧Φs from ≈
    denote_phis (σ from)
    (List.map (fun '(x, φ) => (x, phi_rename σ φ)) φs).
Proof.
  induction φs as [| φ φs IH].
  - reflexivity.
  - destruct φ as [x φ].
    rewrite denote_phis_cons.
    setoid_rewrite IH.
    cbn [List.map].
    rewrite denote_phis_cons.
    apply eutt_clo_bind with (UU := Logic.eq).
    rewrite denote_phi_rename; [reflexivity |].
    now inversion HSafe.
    intros ?? <-.
    reflexivity.
    now inversion HSafe.
Qed.

Lemma bk_phi_rename_eutt :
    forall bk σ from, σφsSafe σ bk.(blk_phis) from ->
      (* dom_renaming σ (outs g2) (outs g2') -> *)
      ⟦ bk ⟧b from ≈ ⟦ bk_phi_rename σ bk ⟧b (σ from).
Proof.
  intros [] * SAFE.
  unfold bk_phi_rename.
  simpl.
  eapply eutt_clo_bind.
  rewrite denote_phis_rename;cycle 1. apply SAFE.
  reflexivity.
  intros ? ? <-. reflexivity.
Qed.

(* Lemma find_block_some_ocfg_rename: forall g id b σ,
  find_block g id = Some b ->
  find_block (ocfg_rename σ g) id = Some (bk_phi_rename σ b).
Proof.
  induction g as [| b' g IH]. now cbn.
  intros * FIND.
  (* unfold find_block, List.find in IH. *)
  unfold find_block, List.find in FIND.
  unfold find_block, List.find.
  break_match_hyp.
  - cbn. rewrite Heqb0. now inversion FIND.
  - cbn. rewrite Heqb0. apply IH. apply FIND.
Qed. *)

Definition σbksSafe σ (g: ocfg) from : Prop :=
  Forall (fun x => σφsSafe σ (x.(blk_phis)) from) g.

Theorem denote_ocfg_equiv (g1 g2 g2' : ocfg) (σ : bk_renaming) :
  let TO  := (outputs g1) ∩ (inputs g2) in
  let TO' := (outputs g1) ∩ (inputs g2') in
  let nTO := inputs g2 \ TO in
  TO = TO' ->
  wf_ocfg_bid (g1 ++ g2) -> wf_ocfg_bid (ocfg_rename σ g1 ++ g2') ->
  dom_renaming σ (outs g2) (outs g2') ->
  denote_ocfg_equiv_cond g1 g2 g2' TO σ ->
  forall from from' to,
  from' = σ from ->
  (* List.In to (TO ++ inputs g1) -> *)
  ~ to ∈ nTO -> ~ from ∈ nTO -> σbksSafe σ g1 from ->
  ⟦g1 ++ g2⟧bs (from,to) ≈ ⟦ocfg_rename σ g1 ++ g2'⟧bs (from', to).
Proof.
  einit.
  ecofix cih.
  clear cihH.
  intros * EQ WF WFσ DOMσ * hIN * EQσ tNIN fNIN SAFE.
  remember ((outputs g1) ∩ (inputs g2)) as TO.
  (* Either we are in the 'visible' graph or not. *)
  case (raw_id_in to (TO ++ inputs g1)) as [tIN'|tNIN'].
  (* Either we enter g1 or not *)
  - pose proof (in_app_or _ _ _ tIN') as [tIN|tIN]; cycle 1.
    * (* if we enter g1: then process [g1], and get back to the whole thing *)
      pose proof find_block_in_inputs _ _ tIN as [bk tFIND].
      pose proof find_block_some_app g1 g2 _ tFIND as FIND.
      rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND].
      pose proof find_block_some_ocfg_rename _ _ _ σ tFIND as FINDσ.
      pose proof find_block_some_app _ g2' _ FINDσ as FIND'.
      rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND'].

    (* Then we start with a first block and then remaining of processing g1 *)
      (* subst. *)
      ebind.
      econstructor.
      subst.
      apply bk_phi_rename_eutt. {
        unfold σφsSafe. apply Forall_forall. intros [e φ] IN. split.
        admit.
      }
      (* admit. *)
      intros [] ? <-.
      (* + rewrite ? bind_tau. *)
      + assert (to = σ to). {
          destruct DOMσ as [in_dom out_dom].
          symmetry. apply out_dom. unfold outs.
          (* Search inputs app. *)
          eapply wf_ocfg_app_not_in_r. apply tIN. now apply wf_ocfg_commut.
        }
        etau.
        ebase.
        right.
        apply cihL; auto.
        (* Generalize goal with an equality to avoid issue with unification (DONE)*)
        admit.
      + eret.
    * subst TO. generalize tIN; intros tmp; apply cap_correct in tmp as [tINo tINi].
      rewrite (@denote_ocfg_prefix_eq_itree g1 g2 nil (g1 ++ g2) from to); cycle 1.
      now rewrite app_nil_r. trivial.
      rewrite (@denote_ocfg_prefix_eq_itree (ocfg_rename σ g1) g2' nil (ocfg_rename σ g1 ++ g2') from' to); cycle 1.
      now rewrite app_nil_r. trivial.
      ebind; econstructor.
      clear - hIN; clear cihL.
      unfold denote_ocfg_equiv_cond in hIN.
      rewrite EQσ; apply hIN; auto.
      intros [[] |] [[] |] INV; try now inv INV.
      inv INV.
      destruct H1 as (INV & <- & ->). {
        (* Extract a lemma? *)
        (* if we enter g1: then process [g1], and get back to the whole thing *)
        (* assert (exists bk, find_block (g1 ++ g2) b2 = Some bk) as (bk & FIND) by admit. *)
        pose proof find_block_in_inputs _ _ INV as [bk tFIND].
        pose proof find_block_some_app g1 g2 _ tFIND as FIND.
        rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND].
        pose proof find_block_some_ocfg_rename _ _ _ σ tFIND as FINDσ.
        pose proof find_block_some_app _ g2' _ FINDσ as FIND'.
        rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND'].

        (* Then we start with a first block and then remaining of processing g1 *)
        (* subst. *)
        ebind.
        econstructor.
        subst.
        apply bk_phi_rename_eutt.
        admit.
        intros [] ? <-.
        (* + rewrite ? bind_tau. *)
        + assert (b2 = σ b2). {
            destruct DOMσ as [in_dom out_dom].
            symmetry. apply out_dom. unfold outs.
            (* Search inputs app. *)
            eapply wf_ocfg_app_not_in_r. apply INV. now apply wf_ocfg_commut.
          }
          etau.
          ebase.
          right.
          apply cihL; auto.
          (* Generalize goal with an equality to avoid issue with unification (DONE)*)
          admit.
        + eret.
      }
  - rewrite denote_ocfg_unfold_not_in_eq_itree.
    rewrite denote_ocfg_unfold_not_in_eq_itree.
    assert (from = σ from) by admit. (*Faux admit?*)
    subst. rewrite <- H. reflexivity.
    admit. admit.

    (* pose proof find_block_in_inputs _ _ tIN as [bk FIND]. *)
    (* assert (exists bk', find_block (ocfg_rename σ g1) to = Some bk' /\ *)
    (*                bk' = bk_phi_rename σ bk) as (bk' & FIND' & EQ') by admit. *)
    (* rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND]. *)
    (* rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND']. *)
    (* rewrite !bind_bind. *)
    (* subst. *)

    (* rewrite (@denote_ocfg_prefix_eq_itree nil g1 g2 (g1 ++ g2) from to). *)
    (* 2,3: admit. *)
    (* rewrite (@denote_ocfg_prefix_eq_itree nil (ocfg_rename σ g1) g2' (ocfg_rename σ g1 ++ g2') (σ from) to). *)
    (* 2, 3: admit. *)


  (*   refine (sum_rel (fun x y => y = σ x) Logic.eq). *)


  (* - rewrite (@denote_ocfg_prefix_strong g1 g2 nil (g1 ++ g2) from to). *)
  (*   2,3: admit. *)
  (*   rewrite (@denote_ocfg_prefix_strong (ocfg_rename σ g1) g2' nil (ocfg_rename σ g1 ++ g2') from to). *)
  (*   2, 3: admit. *)
  (*   (* unfold denote_ocfg_equiv_cond in hIN. *) *)
  (*   destruct (hIN from to tIN) as [[x [RET RET']]|[from' [to' [t'IN [RET RET']]]]]; rewrite RET, RET'. *)
  (*   * admit. *)
  (*   * admit. *)

  (* -
    rewrite (@denote_ocfg_prefix g1 g2 nil (g1 ++ g2) from to).
    2,3: admit.
    rewrite (@denote_ocfg_prefix (ocfg_rename σ g1) g2' nil (ocfg_rename σ g1 ++ g2') from to).
    2,3: admit.
    assert (exists b', find_block g2' to = Some b') as [b' LU'] by admit.
    subst TO. apply cap_correct in tIN as [tINo tINi]. apply find_block_in_inputs in tINi as [b bIN]. vjmp. 2: vjmp.
    * apply find_block_app_r_wf; trivial. apply bIN.
    * apply find_block_app_r_wf; trivial. apply LU'.
    *
      admit.
  - apply find_block_in_inputs in tIN as [b bIN]. vjmp. 2: vjmp.
    * apply find_block_app_l_wf; trivial. apply bIN.
    * apply find_block_app_l_wf; trivial. assert (bIN': find_block (ocfg_rename σ g1) to = Some b). admit. apply bIN'.
    * admit. *)
Admitted.

Theorem Denotation_BlockFusion_correct (G G':map_cfg) A B f to:
  wf_map_cfg G ->
  to <> B.(blk_id) ->
  f <> A.(blk_id) ->
  (A, (B, G')) ∈ (MatchAll (BlockFusion □) G) ->
  denotation_map_cfg G (f, to) ≈
  denotation_map_cfg (update G' (single (fusion A B))) (f, to).
Proof.
  intros * WF ineq1 ineq2 IN.
  apply Pattern_BlockFusion_correct in IN as (G1 & IN & FUS); auto.
  apply Pattern_Graph_correct in IN; subst.
  destruct FUS as [EQ LUA LUB PRED SUCC].
  apply bar.
  set (g := map_cfg_to_ocfg G).
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
  - admit.
Admitted.
*)