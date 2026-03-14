(*  basic_cpos — Worked examples: constructing and using basic CPOs.

    This file builds a guided tour of the core CPO constructions,
    starting from ground-type partial orders and culminating in the
    Kleene fixed-point theorem on a function space.

    Contents:
    - §1  Unit PointedCPO — the trivial one-point domain
    - §2  nat_inf (N U {infty}) — a pointed CPO
    - §3  Discrete bool — the flat boolean domain
    - §4  Product CPOs — pointwise order on pairs
    - §5  Lifted nat — adding a fresh bottom via option
    - §6  Function spaces — continuous endomorphisms of nat_inf
    - §7  The Kleene fixed-point theorem — computing fixp on nat_inf
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Instances Require Import Discrete Nat Function.
From DomainTheory.Theory Require Import OrderTheory CPOTheory Products
                                        Lift FunctionSpaces FixedPoints.
From Stdlib Require Import Lia.


(* ================================================================== *)
(*  §1  Unit PointedCPO                                               *)
(* ================================================================== *)
(*
    [unit] carries the trivial order (x <= y := True).  It has exactly
    one element [tt], which serves as both bottom and top.  The supremum
    of every chain is [tt].

    In the library, [unit] is automatically a [PointedCPO.type] via the
    instances registered in [Discrete.v].
*)

Section UnitExamples.

(* Every pair of unit values is related. *)
Example unit_order : (tt : unit) ⊑ tt.
Proof. exact I. Qed.

(* The bottom element of unit is tt. *)
Example unit_bot : (⊥ : unit) = tt.
Proof. reflexivity. Qed.

(* The sup of any chain in unit is tt. *)
Example unit_sup_is_tt (c : chain unit) : ⊔ c = tt.
Proof. reflexivity. Qed.

End UnitExamples.


(* ================================================================== *)
(*  §2  nat_inf — N U {infty} as a PointedCPO                        *)
(* ================================================================== *)
(*
    [nat_inf] extends [nat] with a point at infinity.  Elements are
    [fin n] for each [n : nat] and [infty].  The order extends Peano:

        fin m <= fin n  iff  m <= n
        fin _  <= infty
        infty <= infty

    Bottom element: [fin 0].  Every chain has a supremum: if it
    eventually stabilises at some [fin v], the sup is [fin v];
    otherwise the sup is [infty].
*)

Section NatInfExamples.

(* fin 3 is below fin 7. *)
Example natinf_fin_le : fin 3 ⊑ fin 7.
Proof. rewrite nat_inf_leE. simpl. lia. Qed.

(* Every finite value is below infty. *)
Example natinf_fin_below_infty : fin 42 ⊑ infty.
Proof. exact (fin_le_infty 42). Qed.

(* Bottom is fin 0. *)
Example natinf_bottom : (⊥ : nat_inf) = fin 0.
Proof. reflexivity. Qed.

(* Bottom is below everything. *)
Example natinf_bottom_least_demo : (⊥ : nat_inf) ⊑ fin 5.
Proof. apply nat_inf_bottom_least. Qed.

(* Infty is the top element. *)
Example natinf_infty_top_demo (x : nat_inf) : x ⊑ infty.
Proof. exact (infty_top x). Qed.

End NatInfExamples.


(* ================================================================== *)
(*  §3  Discrete bool — the flat boolean domain                       *)
(* ================================================================== *)
(*
    [bool] under the discrete (equality) order is a CPO.  Two values
    are related iff they are equal: [b1 <= b2  iff  b1 = b2].

    Every chain is constant (forced by the discrete order), so the
    sup is always [c.[0]].
*)

Section DiscreteBoolExamples.

(* true <= true in the discrete order. *)
Example bool_refl : (true : bool) ⊑ true.
Proof. reflexivity. Qed.

(* false is NOT below true — they are incomparable.
   In the discrete order, x <= y iff x = y. *)
Example bool_incomparable : ~ ((false : bool) ⊑ true).
Proof.
  intro H.
  (* In the discrete order, ⊑ unfolds to equality. *)
  discriminate H.
Qed.

End DiscreteBoolExamples.


(* ================================================================== *)
(*  §4  Product CPOs                                                  *)
(* ================================================================== *)
(*
    The product of two CPOs [D * E] carries the pointwise order:

        (a, b) <= (c, d)  iff  a <= c  /\  b <= d

    Projections [pi_1], [pi_2] are continuous, and the pairing
    combinator [<f, g>] yields a continuous map.

    If [D] and [E] are pointed, then [D * E] is pointed with
    bottom [(bot, bot)].
*)

Section ProductExamples.

(* Abbreviation to help HB pick up the right product CPO instance. *)
Local Definition ni_pair := (nat_inf * nat_inf)%type.

(* Pointwise ordering on nat_inf * nat_inf. *)
Example prod_order_demo :
    (fin 1, fin 2) ⊑ (fin 3, fin 4).
Proof.
  split; rewrite nat_inf_leE; simpl; lia.
Qed.

(* Bottom of the product is (fin 0, fin 0). *)
Example prod_bottom_demo :
    (⊥ : ni_pair) = (fin 0, fin 0).
Proof. reflexivity. Qed.

(* Projections are continuous: pi_1 extracts the first component. *)
Example prod_fst_demo :
    π₁ ((fin 3, fin 7) : ni_pair) = fin 3.
Proof. reflexivity. Qed.

(* pi_2 extracts the second component. *)
Example prod_snd_demo :
    π₂ ((fin 3, fin 7) : ni_pair) = fin 7.
Proof. reflexivity. Qed.

End ProductExamples.


(* ================================================================== *)
(*  §5  Lifted nat — adding a fresh bottom via option                 *)
(* ================================================================== *)
(*
    The flat lift [<D>_bot] of a CPO [D] is [option D] with ordering:

        None   <= x            (None is the fresh bottom)
        Some d <= Some d'  iff  d <= d'
        Some d <= None     is  False

    The lift is a pointed CPO with [bot = None].  The unit
    [ret : D ->c <D>_bot] wraps a value in [Some].  The Kleisli
    extension lets us sequence computations through the lift.

    Here we use [bool] as the ground type, giving a flat three-point
    domain: None < Some false, None < Some true, with Some false and
    Some true incomparable.
*)

Section LiftExamples.

(* None is below everything. *)
Example lift_none_demo : (None : ⟨bool⟩⊥) ⊑ Some true.
Proof. exact I. Qed.

(* Some true <= Some true (reflexivity of the inner order). *)
Example lift_some_refl : (Some true : ⟨bool⟩⊥) ⊑ Some true.
Proof. simpl. reflexivity. Qed.

(* Some false is NOT below Some true — they're incomparable. *)
Example lift_some_incomp : ~ ((Some false : ⟨bool⟩⊥) ⊑ Some true).
Proof.
  simpl. intro H.
  discriminate H.
Qed.

(* Bottom of the lift is None. *)
Example lift_bottom : (⊥ : ⟨bool⟩⊥) = None.
Proof. reflexivity. Qed.

(* ret wraps a value: ret true = Some true. *)
Example lift_ret_demo : ret true = Some true.
Proof. reflexivity. Qed.

End LiftExamples.


(* ================================================================== *)
(*  §6  Function spaces                                               *)
(* ================================================================== *)
(*
    The type [D ->c E] of Scott-continuous functions from [D] to [E]
    is itself a CPO under the pointwise order:

        f <= g  iff  forall x, f x <= g x

    Sup is computed pointwise: (sup fs) x = sup_n (fs.[n] x).

    The constant function combinator [cont_const e] is the K combinator:
    it maps every input to [e].
*)

Section FunctionSpaceExamples.

(* The constant function (cont_const (fin 5)) always returns fin 5. *)
Example const_fun_demo :
    cont_const (fin 5) (fin 99 : nat_inf) = fin 5.
Proof. reflexivity. Qed.

(* The identity is below the constant-infty function, pointwise. *)
Example id_le_const_infty :
    @cont_id nat_inf ⊑ cont_const infty.
Proof.
  intro x. simpl. exact (infty_top x).
Qed.

End FunctionSpaceExamples.


(* ================================================================== *)
(*  §7  The Kleene fixed-point theorem                                *)
(* ================================================================== *)
(*
    For a Scott-continuous endomorphism [f : D ->c D] on a pointed CPO,
    the Kleene fixed point [fixp f] is the supremum of the iteration
    chain:

        bot,  f(bot),  f(f(bot)),  ...

    Key properties:
    - [fixp f] is a fixed point:  f (fixp f) = fixp f
    - [fixp f] is the LEAST pre-fixed point:  f x ⊑ x -> fixp f ⊑ x
    - Fixed-point induction:  admissible P  /\  P bot
                              /\  (P x -> P (f x))  implies  P (fixp f)

    We demonstrate on the constant function [cont_const (fin 3)] on
    [nat_inf].  The iteration chain is:

        fin 0,  fin 3,  fin 3,  fin 3,  ...

    and the fixed point is [fin 3].

    For more interesting fixed points with non-trivial iteration
    (e.g. recursive programs whose denotational semantics uses [fixp]),
    see [pcf_examples.v].
*)

Definition c3 : [nat_inf →c nat_inf] := cont_const (fin 3).

(* Iteration: iter c3 n computes c3^n(bot). *)
Example c3_iter0 : iter c3 0 = fin 0.
Proof. reflexivity. Qed.

Example c3_iter1 : iter c3 1 = fin 3.
Proof. reflexivity. Qed.

Example c3_iter2 : iter c3 2 = fin 3.
Proof. reflexivity. Qed.

(* 
   Computing the fixed-point value: since c3 is a fixed point,
   c3 (fixp c3) = fixp c3.  But c3 = cont_const (fin 3) maps
   everything to fin 3, so fixp c3 = fin 3. 
*)
Example c3_fixp_val : fixp c3 = fin 3.
Proof.
  rewrite <- (fixp_is_fixedpoint c3).
  reflexivity.
Qed.

(* fixp c3 is a fixed point. *)
Example c3_fixp_is_fp : c3 (fixp c3) = fixp c3.
Proof. exact (fixp_is_fixedpoint c3). Qed.

(* fixp c3 is the least pre-fixed point: any x with c3 x ⊑ x is above. *)
Example c3_fixp_least (x : nat_inf) :
    c3 x ⊑ x -> fixp c3 ⊑ x.
Proof. exact (fixp_least c3 x). Qed.

(* 
   The least pre-fixed point is the least fixed point.

   For any Scott-continuous f on a pointed CPO:
   - fixp f is a fixed point  (fixp_is_fixedpoint)
   - fixp f ⊑ every pre-fixed point  (fixp_least)

   Every fixed point (f x = x) is trivially a pre-fixed point
   (f x ⊑ x), so fixp f is below every fixed point too. 
*)
Example fixp_least_among_prefixedpoints
    {D : PointedCPO.type} (f : [D →c D]) (x : D) :
    f x ⊑ x -> fixp f ⊑ x.
Proof.
  intro Hfx.
  unfold fixp.
  apply @sup_least; intro n.
  simpl.
  induction n.
  - simpl. apply bottom_least.
  - transitivity (f x).
    + apply @cf_mono. fold (iter f).
      exact IHn.
    + exact Hfx.
Qed.

(* Fixed-point induction: every admissible property that holds at
   bottom and is preserved by c3 holds at fixp c3. *)
Example c3_fixp_ind (P : nat_inf -> Prop) :
    admissible P -> P ⊥ -> (forall x, P x -> P (c3 x)) ->
    P (fixp c3).
Proof. exact (fixp_ind c3 P). Qed.

(* The identity's least fixed point is bottom: every x is a fixed
   point of id, but fixp selects the least one. *)
Example id_fixp_val : fixp (@cont_id nat_inf) = (⊥ : nat_inf).
Proof.
  apply le_antisym.
  - exact (fixp_least (@cont_id nat_inf) ⊥ (le_refl ⊥)).
  - exact (bottom_least _).
Qed.