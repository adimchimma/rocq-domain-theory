(** Discrete cpos

    Simple wrappers re-exporting the discrete CPO construction from
    `TESTCPO.v`.
*)

From phase0_foundations Require Import CPO Order.

Module Discrete.
  Definition discrete_cpo (X : Type) : Cpo.cpo := {|
    Cpo.cpo_pre := (discrete_preorder X) ;
    Cpo.lub_of_chain := fun c => c 0 ;
    Cpo.lub_upper := fun c n => match n with 0 => eq_refl | S _ => eq_refl end ;
    Cpo.lub_least := fun c x H => H 0 ;
  |}.
End Discrete.
