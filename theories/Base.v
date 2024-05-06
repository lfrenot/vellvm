(** This file defines an FMap that uses block_ids as keys. *)

From Vellvm Require Import Syntax.
Require Import List.

Notation blk := (block dtyp).
Notation bid := block_id.
Notation ocfg := (ocfg dtyp).