(** This file contains the tools to prove the correctness of the block fusion optimization.
    It relies on the garantees given by the [BlockFusion] pattern. *)

From Vellvm Require Import Syntax ScopeTheory Semantics Theory Tactics.
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

Definition fusion_code (A B: blk): code dtyp := A.(blk_code) ++ B.(blk_code).

Definition fusion_comments (A B: blk) :=
  match (A.(blk_comments), B.(blk_comments)) with
    | (Some cA, Some cB) => Some (cA++cB)
    | (Some cA, _) => Some cA
    | (_, Some cB) => Some cB
    | (_, _) => None
  end.

Definition fusion (A B: blk): blk := {|
  blk_id         := A.(blk_id);
  blk_phis       := A.(blk_phis);
  blk_code       := fusion_code A B;
  blk_term       := B.(blk_term);
  blk_comments   := fusion_comments A B
|}.

Import SemNotations.
Import SetNotations.
(* todo better representation*)
Definition bk_renaming := bid -> bid.

Definition phi_rename (σ : bk_renaming) (ϕ:  phi dtyp): phi dtyp :=
  match ϕ with
    | Phi τ exps => Phi τ (List.map (fun '(id,e) => (σ id, e)) exps)
  end.

Definition bk_phi_rename (σ : bk_renaming) (b: blk): blk := {|
  blk_id         := b.(blk_id);
  blk_phis       := List.map (fun '(x,φ) => (x,phi_rename σ φ)) b.(blk_phis);
  blk_code       := b.(blk_code);
  blk_term       := b.(blk_term);
  blk_comments   := b.(blk_comments)
|}.

Definition ocfg_rename (σ : bk_renaming) (g: ocfg): ocfg := List.map (bk_phi_rename σ) g.

Record dom_renaming (σ : bk_renaming) (from to : list bid) : Prop :=
  {
    in_dom : forall id, List.In id from -> List.In (σ id) to;
    out_dom : forall id, ~ List.In id from -> (σ id) = id
  }.

(* Nodes that may exit the graph *)

Definition outs (g : ocfg) : list bid := inputs g.

Definition cap {A}: list A -> list A -> list A. Admitted.

Infix "∩" := cap (at level 10).

Lemma cap_correct: forall {A} (x:A) (l l': list A), x ∈ (l ∩ l') <-> x ∈ l /\ x ∈ l'. Admitted.

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

Lemma denote_ocfg_prefix_eq_itree:
  forall (prefix bks' postfix : ocfg) [bks : ocfg] (from to : bid),
    bks = prefix ++ bks' ++ postfix ->
    wf_ocfg_bid bks ->
    ⟦ bks ⟧bs (from, to) ≅
        x_ <- ⟦ bks' ⟧bs (from, to);;
    match x_ with
      | inl x => ⟦ bks ⟧bs x
      | inr x => Ret (inr x)
  end.
Proof.
    intros * ->; revert from to.
    ginit.
    gcofix CIH.
    (* Trouver un certain R, qui contient ton but, et qui est bien «coinductive», c'est à dire forward closed *)

    intros * WF.

    destruct (find_block bks' to) as [bk |] eqn:EQ.
    -
      assert (find_block (prefix ++ bks' ++ postfix) to = Some bk).
      {
        erewrite find_block_app_r_wf; eauto.
        erewrite find_block_app_l_wf; eauto.
        eapply wf_ocfg_bid_app_r; eauto.
      }
      rewrite denote_ocfg_unfold_in_eq_itree; [| exact H].
      rewrite denote_ocfg_unfold_in_eq_itree; [| exact EQ].
      rewrite bind_bind.
      guclo eqit_clo_bind.
      econstructor.
      reflexivity.
      intros [] ? <-.
      + (* we jump *)
        rewrite bind_tau.
        gstep.
        constructor.
        gbase.
        apply CIH; auto.

      + (* we have returned *)
        rewrite bind_ret_l.
        now gstep.
    - rewrite (denote_ocfg_unfold_not_in_eq_itree bks'); auto.
      rewrite bind_ret_l.
      apply Reflexive_eqit_gen_eq.
Qed.

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
                   v <- translate exp_to_instr (⟦φ⟧Φ b);;
                 ⟦φs⟧Φs b;;
                 Subevent.trigger (LocalWrite (fst v) (snd v))
.
Proof.
  intros ???; revert φ; induction φs as [| φhd φs IH].
  - intros [? []].
    cbn.
    rewrite ?bind_bind, ?bind_ret_l.
    break_match_goal.
    2:admit.
    apply eutt_eq_bind.
    intros [].
    rewrite ?bind_bind, ?bind_ret_l.
    cbn.
    rewrite ?bind_bind, ?bind_ret_l.
    repeat setoid_rewrite bind_ret_l.
    match goal with
      |- eutt _ _ ?t => rewrite <- (bind_ret_r t) at 2
    end.
    apply eutt_eq_bind.
    intros []; reflexivity.
  - intros [? []].
    simpl.
    match goal with
      |- context[raise ?s] => generalize s
    end.
    intros s.
    cbn.
    match goal with
      |- context[raise ?s] => generalize s
    end.
    intros s'.
    rewrite ?bind_bind.
    apply eutt_eq_bind.
    intros [].
    rewrite ?bind_bind, ?bind_ret_l.
    cbn.
    specialize (IH φhd).
    cbn in IH.
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

Definition dom_phi (φ: phi dtyp) : list block_id.
Admitted.

Definition σφSafe σ φ : Prop :=
   forall id, id ∈ (dom_phi φ) -> σ id = id \/ ~ (σ id ∈ (dom_phi φ)).

Lemma denote_phi_rename σ φ
  (Hsafe : σφSafe σ φ) :
  forall x b, ⟦ (x, φ) ⟧Φ b ≈ ⟦ (x, phi_rename σ φ) ⟧Φ (σ b).
Proof.
  intros *. destruct φ as [τ φ].
  induction φ as [| [id e] φ IH].
  - reflexivity.
  - cbn.
    match goal with
      |- context[raise ?s] => generalize s
    end.
    intros s.
    destruct (RelDec.rel_dec b id) eqn:EQ.
    + rewrite RelDec.rel_dec_correct in EQ; subst.
      rewrite Util.eq_dec_eq.
      reflexivity.
    + rewrite <- RelDec.neg_rel_dec_correct in EQ.
      assert (RelDec.rel_dec (σ b) (σ id) = false) by admit.
      setoid_rewrite H.
      apply IH.
      admit.
Admitted.

Definition σφsSafe σ (φs : list (local_id * phi dtyp)) : Prop :=
  List.Forall (fun '(_,φ) => σφSafe σ φ) φs.

Lemma denote_phis_rename
  φs σ from
  (HSafe: σφsSafe σ φs) :
  ⟦ φs ⟧Φs from ≈
    denote_phis (σ from)
    (List.map (fun '(x, φ) => (x, phi_rename σ φ)) φs).
Proof.
  induction φs as [| φ φs IH].
  - cbn [List.map].
    rewrite 2 denote_no_phis.
    reflexivity.
  - destruct φ.
    rewrite denote_phis_cons.
    setoid_rewrite IH.
    cbn [List.map].
    rewrite denote_phis_cons.
    apply eutt_clo_bind with (UU := Logic.eq).
    rewrite denote_phi_rename; [reflexivity |].
    admit.
    intros ?? <-.
    reflexivity.
    admit.
Admitted.

Lemma bk_phi_rename_eutt :
    forall bk σ from,
      (* dom_renaming σ (outs g2) (outs g2') -> *)
      ⟦ bk ⟧b from ≈ ⟦ bk_phi_rename σ bk ⟧b (σ from).
Proof.
  intros [] ? ?.
  unfold bk_phi_rename.
  simpl.
  rewrite ?denote_block_unfold.
  eapply eutt_clo_bind.

  eapply eutt_clo_bind.
Admitted.

Theorem denote_ocfg_equiv (g1 g2 g2' : ocfg) (σ : bk_renaming) :
  let TO  := (outputs g1) ∩ (inputs g2) in
  let TO' := (outputs g1) ∩ (inputs g2') in
  let nTO := inputs g2 ∖ TO in
  TO = TO' ->
  wf_ocfg_bid (g1 ++ g2) -> wf_ocfg_bid (ocfg_rename σ g1 ++ g2') ->
  dom_renaming σ (outs g2) (outs g2') ->
  denote_ocfg_equiv_cond g1 g2 g2' TO σ ->
  forall from from' to,
  from' = σ from ->
  (* List.In to (TO ++ inputs g1) -> *)
  ~ to ∈ nTO ->
  ⟦g1 ++ g2⟧bs (from,to) ≈ ⟦ocfg_rename σ g1 ++ g2'⟧bs (from', to).
Proof.
  einit.
  ecofix cih.
  clear cihH.
  intros * EQ WF WFσ DOMσ. intros * hIN. intros * EQσ NIN.
  remember ((outputs g1) ∩ (inputs g2)) as TO.
  (* Either we are in the 'visible' graph or not. *)
  case (raw_id_in to (TO ++ inputs g1)) as [tIN'|tNIN'].
  (* Either we enter g1 or not *)
  - pose proof (in_app_or _ _ _ tIN') as [tIN|tIN]; cycle 1.
    * (* if we enter g1: then process [g1], and get back to the whole thing *)
      assert (exists bk, find_block (g1 ++ g2) to = Some bk) as (bk & FIND) by admit.
      rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND].
      assert (exists bk', find_block (ocfg_rename σ g1 ++ g2') to = Some bk' /\
                    bk' = bk_phi_rename σ bk) as (bk' & FIND' & EQ') by admit.
      rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND'].

    (* Then we start with a first block and then remaining of processing g1 *)
      (* subst. *)
      ebind.
      econstructor.
      subst.
      apply bk_phi_rename_eutt.
      intros [] ? <-.
      (* + rewrite ? bind_tau. *)
      + assert (to = σ to) by admit.
        etau.
        ebase.
        right.
        apply cihL; auto.
        (* Generalize goal with an equality to avoid issue with unification (DONE)*)
        admit.
      + eret.
    * subst TO. generalize tIN; intros tmp; apply cap_correct in tmp as [tINo tINi].
      rewrite (@denote_ocfg_prefix_eq_itree g1 g2 nil (g1 ++ g2) from to).
      2, 3: admit.
      rewrite (@denote_ocfg_prefix_eq_itree (ocfg_rename σ g1) g2' nil (ocfg_rename σ g1 ++ g2') from' to).
      2, 3: admit.
      ebind; econstructor.
      clear - hIN; clear cihL.
      unfold denote_ocfg_equiv_cond in hIN.
      rewrite EQσ; apply hIN; auto.
      intros [[] |] [[] |] INV; try now inv INV.
      inv INV.
      destruct H1 as (INV & <- & ->).
      {
        (* Extract a lemma? *)
        (* if we enter g1: then process [g1], and get back to the whole thing *)
        assert (exists bk, find_block (g1 ++ g2) b2 = Some bk) as (bk & FIND) by admit.
        rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND].
        assert (exists bk', find_block (ocfg_rename σ g1 ++ g2') b2 = Some bk' /\
                         bk' = bk_phi_rename σ bk) as (bk' & FIND' & EQ') by admit.
        rewrite denote_ocfg_unfold_in_eq_itree; [| exact FIND'].

        (* Then we start with a first block and then remaining of processing g1 *)
        (* subst. *)
        ebind.
        econstructor.
        subst.
        apply bk_phi_rename_eutt.
        intros [] ? <-.
        (* + rewrite ? bind_tau. *)
        + assert (b2 = σ b2) by admit.
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
    assert (from = σ from) by admit.
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
