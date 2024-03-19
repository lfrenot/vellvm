From Vellvm Require Import Syntax ScopeTheory Semantics.
From ITree Require Import ITree Eq.
From Pattern Require Import IdModule MapCFG Patterns BlockFusion.
Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import List.
Import TopLevelBigIntptr InterpretationStack.
Import ListNotations.
Import Map MapF MapF.P MapF.P.F.
Import IdOT MapCFG Head Focus Block Patterns.

(* Denotation definitions *)

Definition ocfg_to_map_cfg (g: ocfg) := List.fold_right (fun b => add_id b) empty g.

Definition map_cfg_to_ocfg (g : map_cfg): ocfg := List.map snd (elements g).

Definition denotation_map_cfg (g : map_cfg) fto :ITreeDefinition.itree instr_E (bid * bid + uvalue) := (denote_ocfg (map_cfg_to_ocfg g)) fto.

(* Block Fusion *)

Definition fusion_code (A B: blk): code dtyp. Admitted.

Definition fusion_comments (A B: blk): option (list String.string). Admitted.

Definition fusion (A B: blk): blk :=
  mk_block A.(blk_id) A.(blk_phis) (fusion_code A B) B.(blk_term) (fusion_comments A B).

Theorem FusionCorrect (G G' G'':map_cfg) A B f to:
  wf_map_cfg G -> to <> B.(blk_id) -> f <> A.(blk_id) ->
  (A, (B, G')) ∈ (MatchAll (BlockFusion □) G) ->
  denotation_map_cfg G (f, to) ≈
  denotation_map_cfg (update G' (single (fusion A B))) (f, to).
Admitted.