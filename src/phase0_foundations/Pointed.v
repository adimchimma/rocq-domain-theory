(** Pointed cpos

    Wrapper for `Pointed` class and `⊥` notation defined in `TESTCPO.v`.
*)

From phase0_foundations Require Import TESTCPO.

Module Pointed.
  Definition Pointed := Pointed.
  Notation "⊥" := bottom.
End Pointed.
