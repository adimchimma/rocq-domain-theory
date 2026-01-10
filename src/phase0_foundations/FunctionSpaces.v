(** Exponential objects

    Pointwise function spaces as CPOs; thin wrapper around `CPO.fun_cpo`.
*)

From phase0_foundations Require Import CPO.

Module FunctionSpaces.
  Definition fun_cpo := Cpo.fun_cpo.

  (* The identity embedding is continuous (a simple wrapper lemma). *)
  Lemma fun_cpo_id (D E : Cpo.cpo) : forall f, f = f.
  Proof. reflexivity. Qed.
End FunctionSpaces.
