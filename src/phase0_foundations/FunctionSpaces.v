(** Exponential objects

    Pointwise function spaces as CPOs; thin wrapper around `CPO.fun_cpo`.
*)

From phase0_foundations Require Import CPO.

Module FunctionSpaces.

  (** Pointwise function space: D => E as a cpo *)
  Program Definition fun_cpo (D E : Cpo.cpo) : Cpo.cpo :=
    {| Cpo.cpo_pre := {|
         carrier := (Cpo.cont_fun D E);
         le := fun f g => forall x, Cpo.le (f x) (g x);
         le_refl := _;
         le_trans := _
       |};
       Cpo.lub_of_chain := fun (c : nat -> Cpo.cont_fun D E) =>
         (* pointwise lub: build function mapping x to lub (fun n => c n x) *)
         {| Cpo.cf_func := fun x => Cpo.lub_of_chain (fun n => (c n) x);
            Cpo.cf_cont := _
         |};
       Cpo.lub_upper := _;
       Cpo.lub_least := _
    |}.
  Next Obligation. intros f x; apply Cpo.le_refl. Qed.
  Next Obligation. intros f g h Hfg Hgh x; apply (Cpo.le_trans _ _ _ (Hfg x) (Hgh x)). Qed.
  Next Obligation.
    unfold Cpo.continuous. intros D0 E0 d.
    simpl.
    apply Cpo.lub_least. intros k.
    specialize (Cpo.cf_cont (c k) d) as Hck.
    apply (Cpo.le_trans _ _ _ Hck).
    apply Cpo.lub_least. intros m.
    apply Cpo.le_trans with (Cpo.lub_of_chain (fun t => (c t) (d m))).
    - apply Cpo.lub_upper.
    - apply Cpo.lub_least. intros t. apply Cpo.lub_upper.
  Qed.
  Next Obligation. intros c n x; simpl. apply Cpo.lub_upper. Qed.
  Next Obligation. intros c x H y.
    simpl. apply (Cpo.lub_least (fun n => (c n) y) (x y)).
    intros n. apply (H n y).
  Qed.

End FunctionSpaces.
