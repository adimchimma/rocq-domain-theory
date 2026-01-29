(** Pointed cpos

    Wrapper for `Pointed` class and `⊥`.
*)

From phase0_foundations Require Import CPO Order.
Import Order.

Module Pointed.
  Definition Pointed := Cpo.Pointed.
  Notation "⊥" := (@Cpo.bottom _ _).
End Pointed.
