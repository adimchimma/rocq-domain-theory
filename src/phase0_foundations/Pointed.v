(** Pointed cpos

    Wrapper for `Pointed` class and `⊥` notation defined in `TESTCPO.v`.
*)

From phase0_foundations Require Import CPO Order.
Import Order.

Module Pointed.
  Definition Pointed := Cpo.Pointed.
  Notation "⊥" := (@Cpo.bottom _ _).
End Pointed.
