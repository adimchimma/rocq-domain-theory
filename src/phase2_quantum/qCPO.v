(** qCPO category

    Minimal qCPO API to support tests in `test/test_quantum.v`.
*)

From Coq Require Import Init.Prelude.
From Coq Require Import Lists.List.
From phase0_foundations Require Import Order.

Module qCPO.
  Section Defs.
    (* Minimal representation: a qCPO is a Type with a lub operator for chains. *)
    Record t := mk {
      carrier : Type;
      chain : Type := nat -> carrier;
      lub : chain -> carrier;
      lub_upper : forall (c : chain) (n : nat), c n = c n -> True; (* placeholder property *)
    }.

    Definition qCPO_has_lub := True.
  End Defs.
End qCPO.

