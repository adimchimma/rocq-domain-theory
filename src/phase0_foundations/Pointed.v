(** Pointed cpos

    Wrapper for `Pointed` class and `⊥` notation defined in `TESTCPO.v`.
*)

From phase0_foundations Require Import CPO.

Module Pointed.
  Definition Pointed := Cpo.Pointed.
  Notation "⊥" := bottom.
End Pointed.
