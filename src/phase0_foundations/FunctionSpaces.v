(** Exponential objects

    Pointwise function spaces as CPOs; minimal implementation.
*)

From phase0_foundations Require Import CPO Continuous Order.

Module FunctionSpaces.

  (** Helper: create the pointwise order *)
  Definition pointwise_le : forall (D E : Cpo.cpo) (f g : Continuous.cont_fun D E), Prop :=
    fun D E f g => 
      forall x, Order.le (Cpo.cpo_pre E) 
        (Order.mf_func _ _ (Continuous.cf_mfun D E f) x) 
        (Order.mf_func _ _ (Continuous.cf_mfun D E g) x).

  (** Helper: pointwise order is reflexive *)
  Definition pointwise_refl : forall (D E : Cpo.cpo) (f : Continuous.cont_fun D E), pointwise_le D E f f :=
    fun D E f x => Order.le_refl (Cpo.cpo_pre E) (Order.mf_func _ _ (Continuous.cf_mfun D E f) x).

  (** Helper: pointwise order is transitive *)
  Definition pointwise_trans : forall (D E : Cpo.cpo) (f g h : Continuous.cont_fun D E),
    pointwise_le D E f g -> pointwise_le D E g h -> pointwise_le D E f h :=
    fun D E f g h Hfg Hgh x => 
      Order.le_trans (Cpo.cpo_pre E) 
        (Order.mf_func _ _ (Continuous.cf_mfun D E f) x) 
        (Order.mf_func _ _ (Continuous.cf_mfun D E g) x) 
        (Order.mf_func _ _ (Continuous.cf_mfun D E h) x) 
        (Hfg x) (Hgh x).

  (** Pointwise function space: D => E as a cpo *)
  (* TODO: Implement pointwise lubs properly with chains *)
  Axiom fun_cpo_lub : forall (D E : Cpo.cpo) 
    (fun_pre : Order.preorder),
    Order.chain fun_pre -> Order.carrier fun_pre.
  
  Axiom fun_cpo_lub_upper : forall (D E : Cpo.cpo) 
    (fun_pre : Order.preorder)
    (c : Order.chain fun_pre) (n : nat),
    Order.le fun_pre (Order.ch fun_pre c n) (fun_cpo_lub D E fun_pre c).
    
  Axiom fun_cpo_lub_least : forall (D E : Cpo.cpo) 
    (fun_pre : Order.preorder)
    (c : Order.chain fun_pre) (x : Order.carrier fun_pre),
    (forall n, Order.le fun_pre (Order.ch fun_pre c n) x) ->
    Order.le fun_pre (fun_cpo_lub D E fun_pre c) x.
  
  Definition fun_cpo (D E : Cpo.cpo) : Cpo.cpo :=
    let fun_pre := {|
         Order.carrier := Continuous.cont_fun D E ;
         Order.le := pointwise_le D E ;
         Order.le_refl := pointwise_refl D E ;
         Order.le_trans := pointwise_trans D E
       |} in
    {| 
       Cpo.cpo_pre := fun_pre ;
       Cpo.lub_of_chain := fun_cpo_lub D E fun_pre ;
       Cpo.lub_upper := fun_cpo_lub_upper D E fun_pre ;
       Cpo.lub_least := fun_cpo_lub_least D E fun_pre
    |}.

End FunctionSpaces.
