(** Hierarchy-Builder instances

    This module is part of the rocq-domain-theory project.
*)

From HB Require Import structures.
Require Import Hierarchies.
From Coq Require Import Nat.

(* Minimal example: declare nat as a Magma via hasOp instance *)
HB.instance Definition _ := hasOp.Build nat Nat.add.
