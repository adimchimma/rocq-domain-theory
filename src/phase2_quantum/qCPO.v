(** qCPO category

    Minimal qCPO API to support tests in `test/test_quantum.v`.
*)

Module qCPO.
  Section Defs.
    (* Minimal representation: a qCPO is a Type with a lub operator for chains. *)
    Record t := mk {
      carrier : Type;
      chain : Type := nat -> carrier;
      lub : chain -> carrier;
      lub_upper : forall (c : chain) (n : nat), True; (* placeholder property *)
    }.

    Definition cpo := t.

    Definition qCPO_has_lub := True.
  End Defs.
End qCPO.

