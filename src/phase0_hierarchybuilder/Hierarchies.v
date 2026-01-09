(** Algebraic hierarchy

    This module is part of the rocq-domain-theory project.
*)

From HB Require Import structures.

(* Minimal example: a magma structure with a binary operation *)
HB.mixin Record hasOp (T : Type) := { op : T -> T -> T }.
HB.structure Definition Magma := { T of hasOp T }.

(* Inspect what HB declares for Magma *)
HB.about Magma.

(* Export a short lemma to exercise the module *)
Print Magma.type.
