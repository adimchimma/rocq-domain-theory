(** Fixed point operators

    Re-export of fixed-point infrastructure built on `CPO.v` and simple helper lemmas.
*)

From phase0_foundations Require Import CPO.

Module FixedPoints.
  Export Cpo.

  (* The fixpoint operator and induction principle are available in Cpo.Fixpoint *)
  Ltac done := trivial.
End FixedPoints.
