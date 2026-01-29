(** Hierarchy-Builder instances

    This module is part of the rocq-domain-theory project.
*)

From HB Require Import structures.
From phase0_hierarchybuilder Require Import Hierarchies.

(* Minimal example: declare nat as a Magma via hasOp instance *)
Fixpoint nat_add (n m : nat) : nat :=
    match n with
    | 0 => m
    | S n' => S (nat_add n' m)
    end.

HB.instance Definition _ := hasOp.Build nat nat_add.
