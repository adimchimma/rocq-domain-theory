(** Continuous functions

    Basic definitions and simple lemmas for continuity (wrappers around `CPO.v`).
*)

From phase0_foundations Require Import CPO.

Module Continuous.
  (* Re-export the continuous predicate from Cpo *)
  Definition continuous := Cpo.continuous.

  (* Identity is continuous *)
  Lemma id_continuous (D E : Cpo.cpo) : continuous D D (fun x => x).
  Proof. intros c; apply Cpo.le_refl. Qed.
End Continuous.
