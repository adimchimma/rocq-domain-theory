(** Product constructions

    Thin wrapper around `CPO.prod_cpo` implemented in `CPO.v`.
*)

From phase0_foundations Require Import CPO.

Module Products.

  (** Product cpo: pointwise order and lubs *)
  Program Definition prod_cpo (A B : Cpo.cpo) : Cpo.cpo :=
    {| Cpo.cpo_pre := {|
         carrier := (Cpo.carrier A * Cpo.carrier B);
         le := fun p q => Cpo.le (fst p) (fst q) /\ Cpo.le (snd p) (snd q);
         le_refl := _;
         le_trans := _
       |};
       Cpo.lub_of_chain := fun c => (Cpo.lub_of_chain (fun n => fst (c n)), Cpo.lub_of_chain (fun n => snd (c n)));
       Cpo.lub_upper := _;
       Cpo.lub_least := _
    |}.
  Next Obligation. intros [a b]; split; apply Cpo.le_refl. Qed.
  Next Obligation. intros [a1 b1] [a2 b2] [a3 b3] [H12a H12b] [H23a H23b]; split; apply (Cpo.le_trans _ _ _ H12a H23a) || apply (Cpo.le_trans _ _ _ H12b H23b). Qed.
  Next Obligation. intros c n; simpl; split; [apply Cpo.lub_upper| apply Cpo.lub_upper]. Qed.
  Next Obligation. intros c [a b] H; simpl; split; [apply (Cpo.lub_least (fun n => fst (c n)) a); intros n; destruct (H n) as [Hf _]; apply Hf | apply (Cpo.lub_least (fun n => snd (c n)) b); intros n; destruct (H n) as [_ Hs]; apply Hs]. Qed.

End Products.
