(** Discrete cpos (temporary unit instance)

    Minimal, trivially ordered unit cpo used for simple tests.
*)

From phase0_foundations Require Import CPO Order.
Import Order.

Module Discrete.
  Definition unit_preorder : preorder := {|
    carrier := unit ;
    le := fun _ _ => True ;
    le_refl := fun _ => I ;
    le_trans := fun _ _ _ _ _ => I ;
  |}.

  Definition unit_cpo : Cpo.cpo := {|
    Cpo.cpo_pre := unit_preorder ;
    Cpo.lub_of_chain := fun _ => tt ;
    Cpo.lub_upper := fun _ _ => I ;
    Cpo.lub_least := fun _ _ _ => I ;
  |}.
End Discrete.
