(** Product constructions

    Thin wrapper around `CPO.prod_cpo` implemented in `CPO.v`.
*)

From phase0_foundations Require Import CPO.

Module Products.
  Definition prod_cpo := Cpo.prod_cpo.

  (* Projection convenience lemmas can be added later. *)
End Products.
