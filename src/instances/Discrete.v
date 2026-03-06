(*  Discrete CPO Instances

    Two basic CPO constructions that serve as building blocks throughout
    the library.

    §1  [unit] as a pointed CPO — terminal object in CPO.
        Order:  [fun _ _ => True] — the indiscrete order on one element.
        Sup:    [⊔ c = tt] for every chain [c].
        Bottom: [tt].

    §2  The [discrete] type — a newtype wrapper.

    §3  Order on [discrete A] — the equality order.
        [x ⊑ y  ↔  x = y].

    §4  Chain theory for [discrete A].
        Every chain is constant: [c.[n] = c.[0]] for all [n].

    §5  CPO structure on [discrete A].
        [⊔ c = c.[0]] for every chain [c : chain (discrete A)].
        No bottom in general; apply [Lift] to obtain a pointed domain.

    §6  [discrete unit] as a pointed CPO.
        [tt] is the unique element and therefore the bottom.
        Note: [discrete unit] and [unit] are definitionally equal, but
        HB dispatches instances by syntactic head, so both types need
        their own registrations.

    §7  Universal property: every function out of a discrete CPO is
        Scott-continuous.
        Equivalently, [discrete A] is the free CPO on the set [A]: the
        inclusion [to_discrete : A -> discrete A] is initial among
        functions from [A] into CPOs.

    This is [src/instances/Discrete.v].

    Imports:
      [src/structures/Order.v]     — HasLe, IsPreorder, IsPartialOrder,
                                     chain, mono_fun, monotone, map_chain
      [src/structures/CPO.v]       — HasSup, IsCPO, CPO,
                                     HasBottom, IsPointed, PointedCPO
      [src/structures/Morphisms.v] — cont_fun, Build_cont_fun, [D →c E]

    Phase coverage:
      Phase 0 — all sections

    References:
      Abramsky & Jung, "Domain Theory" (1994), Example 2.1.4 (discrete CPO).
      Benton & Kennedy, "Relational Parametricity for Value Types" (2001) §2.1.
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.


(* ================================================================== *)
(*  §1  Unit CPO                                                       *)
(* ================================================================== *)

(*
    The order on [unit] is the indiscrete order [fun _ _ => True]:
    every pair of elements is related.  Since [unit] has only one
    element, this is both the finest and coarsest possible order, and
    all CPO axioms reduce to [True].

    [unit] is the terminal object in CPO: for any CPO [D] there is
    exactly one continuous function [[D →c unit]], namely [fun _ => tt].

    Instance registration order follows DD-008:
      HasLe → IsPreorder → IsPartialOrder → HasSup → IsCPO
        → HasBottom → IsPointed.
*)

Definition unit_le (x y : unit) : Prop := True.

Lemma unit_le_refl (x : unit) : unit_le x x.
Proof. 
  exact I. 
Qed.

Lemma unit_le_trans (x y z : unit) :
    unit_le x y -> unit_le y z -> unit_le x z.
Proof. 
  intros _ _; exact I. 
Qed.

Lemma unit_le_antisym (x y : unit) :
    unit_le x y -> unit_le y x -> x = y.
Proof. 
  intros _ _; destruct x, y; reflexivity. 
Qed.

HB.instance Definition unit_HasLe :=
  HasLe.Build unit unit_le.

HB.instance Definition unit_IsPreorder :=
  IsPreorder.Build unit unit_le_refl unit_le_trans.

HB.instance Definition unit_IsPartialOrder :=
  IsPartialOrder.Build unit unit_le_antisym.

(*
    The supremum of any chain in [unit] is [tt].  Since every element of
    [unit] is [tt], both axioms reduce to [True].

    We state the axiom lemmas with the raw [unit_sup] function and
    register [HasSup] after, following the convention of [Lift.v] §1
    and [Products.v] §2.
*)

Definition unit_sup (c : chain unit) : unit := tt.

Lemma unit_sup_upper (c : chain unit) (n : nat) :
    c.[n] ⊑ unit_sup c.
Proof. 
  exact I. 
Qed.

Lemma unit_sup_least (c : chain unit) (x : unit)
    (Hub : forall n, c.[n] ⊑ x) : unit_sup c ⊑ x.
Proof. 
  destruct x; exact I. 
Qed.

HB.instance Definition unit_HasSup :=
  HasSup.Build unit unit_sup.

HB.instance Definition unit_IsCPO :=
  IsCPO.Build unit unit_sup_upper unit_sup_least.

(*  [unit] is pointed: [tt] is the least (and only) element. *)

HB.instance Definition unit_HasBottom :=
  HasBottom.Build unit tt.

Lemma unit_bottom_least (x : unit) : ⊥ ⊑ x.
Proof. 
  exact I. 
Qed.

HB.instance Definition unit_IsPointed :=
  IsPointed.Build unit unit_bottom_least.

(*  The supremum is always [tt]. *)
Lemma unit_sup_tt (c : chain unit) : ⊔ c = tt.
Proof. 
  destruct (⊔ c); reflexivity. 
Qed.


(* ================================================================== *)
(*  §2  The discrete type                                              *)
(* ================================================================== *)

(*
    [discrete A] is a newtype wrapper around [A]: definitionally
    [discrete A = A], so [to_discrete] and [from_discrete] are both the
    identity function.  The wrapper is necessary so that HB can attach
    the equality order to [discrete A] without registering a global
    [HasLe] instance on every type [A].
*)
Definition discrete (A : Type) : Type := A.

Definition to_discrete   {A : Type} (a : A) : discrete A := a.
Definition from_discrete {A : Type} (d : discrete A) : A  := d.


(* ================================================================== *)
(*  §3  Order on [discrete A]                                         *)
(* ================================================================== *)

(*
    The discrete order on [A] identifies [⊑] with propositional equality:
    [x ⊑ y  ↔  x = y].  It is the finest partial order: only [x ⊑ x]
    holds (A&J Example 2.1.4).

    Design note: the section contains only the raw predicate and its
    three order proofs.  All HB instance registrations appear outside
    the section (after [End DiscreteOrder]) with an explicit [(A : Type)]
    parameter, following the [Products.v] and [Lift.v] conventions.
    [Arguments] declarations immediately after the section restore
    implicit treatment of [A].
*)

Section DiscreteOrder.
Variable A : Type.

(*  The order predicate: [x ⊑ y] iff [x = y].  *)
Definition discrete_le (x y : discrete A) : Prop := x = y.

Lemma discrete_le_refl (x : discrete A) : discrete_le x x.
Proof. 
  reflexivity. 
Qed.

Lemma discrete_le_trans (x y z : discrete A) :
    discrete_le x y -> discrete_le y z -> discrete_le x z.
Proof.
  unfold discrete_le. 
  exact (@eq_trans (discrete A) x y z). 
Qed.

(*
    Antisymmetry is immediate: [discrete_le x y] is [x = y], which
    already gives the conclusion.  The reverse hypothesis is not used.
*)
Lemma discrete_le_antisym (x y : discrete A) :
    discrete_le x y -> discrete_le y x -> x = y.
Proof. 
  intros Hxy _. exact Hxy. 
Qed.

End DiscreteOrder.

(*
    Restore implicit treatment of [A] so that downstream code does not
    need to supply it manually.
*)
Arguments discrete_le         {A} x y.
Arguments discrete_le_refl    {A} x.
Arguments discrete_le_trans   {A} x y z _ _.
Arguments discrete_le_antisym {A} x y _ _.

(*
    Register the order structure on [discrete A] for all [A : Type].
    After these instances, [⊑] on [discrete A] denotes [discrete_le].
*)
HB.instance Definition discrete_HasLe (A : Type) :=
  HasLe.Build (discrete A) discrete_le.

HB.instance Definition discrete_IsPreorder (A : Type) :=
  IsPreorder.Build (discrete A) discrete_le_refl discrete_le_trans.

HB.instance Definition discrete_IsPartialOrder (A : Type) :=
  IsPartialOrder.Build (discrete A) discrete_le_antisym.

(*
    The order on [discrete A] is definitionally propositional equality.
    This lemma provides a named rewriting rule for converting between
    the [⊑] notation and [=] in proof contexts.
*)
Lemma discrete_le_iff {A : Type} (x y : discrete A) :
    x ⊑ y <-> x = y.
Proof.
  split; auto. 
Qed.


(* ================================================================== *)
(*  §4  Chain theory for [discrete A]                                 *)
(* ================================================================== *)

(*
    Now that [discrete A] is a [Preorder.type], [ch_mono] applied to
    a chain [c : chain (discrete A)] yields an element of [⊑] on
    [discrete A], which is a propositional equality.  Consequently,
    every chain in the discrete order is forced to be constant.

    [discrete_chain_const] is the key structural lemma: every chain
    stabilises at its zeroth term.  It is used in §5 to compute sups
    and in §7 to prove that every function out of [discrete A] is
    continuous.
*)

Section DiscreteChain.
Variable A : Type.

(*
    Proof: [ch_mono c 0 n _ : c.[0] ⊑ c.[n]].  In [discrete A],
    [⊑] is [eq], so this gives [c.[0] = c.[n]]; [symmetry] yields
    [c.[n] = c.[0]] as stated.
*)
Lemma discrete_chain_const (c : chain (discrete A)) (n : nat) :
    c.[n] = c.[0].
Proof.
  symmetry. exact (ch_mono c 0 n (le_0_n n)).
Qed.

End DiscreteChain.

Arguments discrete_chain_const {A} c n.

(*  Any two positions in a discrete chain agree.  *)
Lemma discrete_chain_eq {A : Type} (c : chain (discrete A)) (m n : nat) :
    c.[m] = c.[n].
Proof.
  rewrite discrete_chain_const.
  rewrite <- (discrete_chain_const c n).
  reflexivity.
Qed.


(* ================================================================== *)
(*  §5  CPO structure on [discrete A]                                 *)
(* ================================================================== *)

(*
    Since every chain is constant at its zeroth element (§4), the
    supremum is simply [c.[0]].

    Following the established library pattern (cf. [Lift.v] §3,
    [Products.v] §2), we state and prove [discrete_sup_upper] and
    [discrete_sup_least] using the raw [discrete_sup] function *before*
    registering [HasSup].  Once [HasSup] is registered, [discrete_sup c]
    and [⊔ c] are definitionally equal, so [IsCPO.Build] accepts the
    lemmas without any unfolding in the goal.
*)

Section DiscreteSup.
Variable A : Type.

(*  The supremum function: return the zeroth element.  *)
Definition discrete_sup (c : chain (discrete A)) : discrete A := c.[0].

(*
    Upper bound: [c.[n] = c.[0] = discrete_sup c].
    The equality [c.[n] ⊑ discrete_sup c] is [c.[n] = c.[0]], which is
    exactly [discrete_chain_const c n].
*)
Lemma discrete_sup_upper (c : chain (discrete A)) (n : nat) :
    c.[n] ⊑ discrete_sup c.
Proof.
  unfold discrete_sup.
  exact (discrete_chain_const c n).
Qed.

(*
    Least upper bound: any upper bound [x] satisfies [c.[0] ⊑ x]
    by instantiating [Hub] at [n = 0].
*)
Lemma discrete_sup_least (c : chain (discrete A)) (x : discrete A)
    (Hub : forall n, c.[n] ⊑ x) : discrete_sup c ⊑ x.
Proof.
  unfold discrete_sup.
  exact (Hub 0).
Qed.

End DiscreteSup.

Arguments discrete_sup       {A} c.
Arguments discrete_sup_upper {A} c n.
Arguments discrete_sup_least {A} c x _.

(*
    Register the CPO structure on [discrete A] for all [A : Type].
    After these instances, [⊔] on [discrete A] denotes [discrete_sup].
    Instance ordering follows DD-008.
*)
HB.instance Definition discrete_HasSup (A : Type) :=
  HasSup.Build (discrete A) discrete_sup.

HB.instance Definition discrete_IsCPO (A : Type) :=
  IsCPO.Build (discrete A) discrete_sup_upper discrete_sup_least.

(*
    The key computational fact: [⊔ c = c.[0]].

    This is the analogue of [unit_sup_tt] for the discrete construction.
    Proof by antisymmetry on the now-registered CPO:
    - [⊔ c ⊑ c.[0]]: every [c.[n] ⊑ c.[0]] by [discrete_chain_const];
      take the sup-least.
    - [c.[0] ⊑ ⊔ c]: [sup_upper] at index 0.
*)
Lemma discrete_sup_eq {A : Type} (c : chain (discrete A)) :
    ⊔ c = c.[0].
Proof.
  apply le_antisym.
  - apply @sup_least; intro n. exact (discrete_chain_const c n).
  - exact (sup_upper c 0).
Qed.


(* ================================================================== *)
(*  §6  Pointed instance for [discrete unit]                          *)
(* ================================================================== *)

(*
    [discrete unit] is a [PointedCPO]: [tt] is the unique element and
    therefore the bottom.

    [tt ⊑ x] in [discrete unit] is [discrete_le tt x = (tt = x)].
    Since [unit] has exactly one element, [x = tt] always, so [tt = x]
    follows by [destruct x; reflexivity].

    Note on instance scope: [discrete unit] and [unit] are definitionally
    equal ([discrete A = A]), but HB's canonical-structure elaboration
    dispatches on the *syntactic head* of the type.  Expressions whose
    inferred type is [unit] use the §1 instances; those whose type is
    [discrete unit] use these.  Both registrations are required for the
    library to behave correctly under both spellings.

    For general [discrete A] with [A] non-trivial, no bottom exists;
    use [Lift (discrete A)] to obtain a pointed domain (A&J §2.1.4).

    Registration order follows DD-008: [discrete_IsCPO] is already
    registered above; we add [HasBottom] then [IsPointed].
*)

HB.instance Definition discrete_unit_HasBottom :=
  HasBottom.Build (discrete unit) tt.

Lemma discrete_unit_bottom_least (x : discrete unit) : ⊥ ⊑ x.
Proof. 
  destruct x; reflexivity. 
Qed.

HB.instance Definition discrete_unit_IsPointed :=
  IsPointed.Build (discrete unit) discrete_unit_bottom_least.


(* ================================================================== *)
(*  §7  Universal property: every map out of a discrete CPO is        *)
(*      Scott-continuous                                               *)
(* ================================================================== *)

(*
    Because chains in [discrete A] are constant (§4), any function
    [f : discrete A -> D] automatically commutes with all chain sups,
    with no conditions on [f].  This is the universal property of the
    discrete CPO: [discrete A] is the *free CPO* on the set [A].

    Concretely, [to_discrete : A -> discrete A] is the universal arrow:
    for any CPO [D] and any function [h : A -> D], there is a unique
    continuous map [[discrete_to_cont h : discrete A →c D]] such that
    [discrete_to_cont h (to_discrete a) = h a] (the computation rule
    holds by [reflexivity] since [to_discrete] is the identity).

    This result belongs in [Discrete.v] rather than [Morphisms.v] because
    it is a property of the [discrete] construction specifically, and is
    immediately useful to consumers of this file (e.g., defining
    denotations of base-type constants in [PCF_Denotational.v]).

    Construction:
      1. [discrete_monotone]      — any [f] is monotone.
      2. [discrete_continuous]    — the induced [mono_fun] is continuous.
      3. [discrete_to_cont]       — packages (1) and (2) as a [cont_fun].
      4. [discrete_to_cont_apply] — the computation rule (by [reflexivity]).
*)

Section DiscreteUniversal.
Context {A : Type} {D : CPO.type}.

(*
    Monotonicity: [x ⊑ y] in [discrete A] is [x = y] (by
    [discrete_le_iff]), so [subst] collapses the goal to [f x ⊑ f x],
    closed by [le_refl].
*)
Lemma discrete_monotone (f : discrete A -> D) :
    monotone (discrete A) D f.
Proof.
  intros x y Hxy.
  inversion Hxy; subst.
  exact (le_refl _).
Qed.

(*
    Continuity: we show [f (⊔ c) = ⊔ (map_chain f_mono c)].
    - Rewrite [⊔ c = c.[0]] via [discrete_sup_eq].
    - Upper bound direction [f(c.[0]) ⊑ ⊔ map_chain]:
        [(map_chain f_mono c).[0] = f(c.[0])], so [sup_upper] at 0 applies.
    - Least bound direction [⊔ map_chain ⊑ f(c.[0])]:
        [sup_least] reduces to showing [f(c.[n]) ⊑ f(c.[0])] for all [n].
        [discrete_chain_const c n : c.[n] = c.[0]] lets us rewrite
        [f(c.[n])] to [f(c.[0])], closed by [le_refl].
*)
Lemma discrete_continuous (f : discrete A -> D) :
    continuous (Build_mono_fun f (discrete_monotone f)).
Proof.
  unfold continuous.
  intro c.
  set (f_mono := Build_mono_fun f (discrete_monotone f)).
  apply le_antisym.
  - exact (sup_upper (map_chain f_mono c) 0).
  - apply sup_least; intro n.
    cbn.
    exact (discrete_monotone f (c.[n]) (c.[0]) (discrete_chain_const c n)).
Qed.

(*
    The universal continuous extension of [f : discrete A -> D].
    The computation rule [discrete_to_cont f x = f x] holds by
    [reflexivity] since [Build_mono_fun] and [Build_cont_fun] are
    definitionally transparent coercions.
*)
Definition discrete_to_cont (f : discrete A -> D) : [discrete A →c D] :=
  Build_cont_fun
    (Build_mono_fun f (discrete_monotone f))
    (discrete_continuous f).

Lemma discrete_to_cont_apply (f : discrete A -> D) (x : discrete A) :
    discrete_to_cont f x = f x.
Proof. 
  reflexivity. 
Qed.

End DiscreteUniversal.