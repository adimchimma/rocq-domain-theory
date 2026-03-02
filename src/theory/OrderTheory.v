(*  OrderTheory

    Phase 0: Derived theory for preorders and partial orders.

    This is [src/theory/OrderTheory.v].  All definitions it needs are
    declared in [src/structures/Order.v]; this file contains only
    _proofs_ and derived constructions.

    Imports:
      [src/structures/Order.v] — Preorder, PartialOrder, chain, mono_fun

    Contents:
    - §1  [pequiv] as a setoid equivalence (reflexivity, symmetry, transitivity)
    - §2  Setoid / Proper instances for [⊑] and [≈] (enables [rewrite])
    - §3  Monotone function lemmas (pointwise equivalence, extensionality)
    - §4  Partial-order consequences (antisymmetry, equality ↔ equivalence)
    - §5  Chain index lemmas (arithmetic lemmas on [c.[n]], const/tail chains)

    Phase coverage:
      Phase 0 — foundational order and chain lemmas
      Phase 1 — no additions planned (enriched theory builds on CPOTheory)
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order.

From Stdlib.Classes Require Import RelationClasses Morphisms.
From Stdlib.Program Require Import Basics.

From Stdlib Require Import PeanoNat.

(* ================================================================== *)
(*   [pequiv] is an equivalence relation                              *)
(* ================================================================== *)
(*
    [pequiv] (notation [x ≈ y]) is defined in [Order.v] as the
    conjunction [x ⊑ y ∧ y ⊑ x].  We prove here that it is a genuine
    equivalence relation on any preorder, and register the corresponding
    Coq [Equivalence] instance so that [rewrite] and [setoid_rewrite]
    work smoothly. 
*)
Section PequivEquivalence.
Context {T : Preorder.type}.

Lemma pequiv_refl (x : T) : x ≈ x.
Proof.
    split; apply le_refl.
Qed.

Lemma pequiv_symm (x y : T) : x ≈ y -> y ≈ x.
Proof.
    intros [HxLEy HyLEx].
    exact (conj HyLEx HxLEy).
Qed.

Lemma pequiv_trans (x y z : T) : x ≈ y -> y ≈ z -> x ≈ z.
Proof.
    intros [HxLEy HyLEx] [HyLEz HzLEy].
    split.
    - exact (le_trans _ _ _ HxLEy HyLEz).
    - exact (le_trans _ _ _ HzLEy HyLEx).
Qed.

(* Introduction: two inequalities give an equivalence. *)
Lemma le_le_pequiv (x y : T) : x ⊑ y -> y ⊑ x -> x ≈ y.
Proof.
    intros HxLEy HyLEx.
    exact (conj HxLEy HyLEx).
Qed.

(* Elimination: extract the two inequalities from an equivalence. *)
Lemma pequiv_le_l (x y : T) : x ≈ y -> x ⊑ y.
Proof.
    intros [H _]; exact H.
Qed.

Lemma pequiv_le_r (x y : T) : x ≈ y -> y ⊑ x.
Proof.
    intros [_ H].
    exact H.
Qed.

End PequivEquivalence.


(* ================================================================== *)
(*   Setoid / Proper instances                                        *)
(* ================================================================== *)
(*
    Registering these instances lets Rocq's [rewrite] tactic work
    under [⊑] and [≈].  The [PreOrder] instance on [leT] is used by
    [transitivity] and by any tactic that needs reflexivity/transitivity
    without going through the named lemmas. 
*)

(* [⊑] forms a [PreOrder] (reflexive, transitive). *)
Global Instance le_preorder_inst {T : Preorder.type} :
    PreOrder (fun x y : T => x ⊑ y).
Proof.
    constructor; red.
    - exact le_refl.
    - exact le_trans.
Qed.

(* [≈] is an [Equivalence] on any preorder. *)
Global Instance pequiv_equiv {T : Preorder.type} :
    Equivalence (@pequiv T).
Proof.
    constructor; red.
    - exact pequiv_refl.
    - exact pequiv_symm.
    - exact pequiv_trans.
Qed.

(*
    Properness of [⊑] with respect to [≈] on both sides.
    This allows [rewrite H] under [⊑] goals when [H : x ≈ x']. 
*)
Global Instance le_pequiv_proper {T : Preorder.type} :
    Proper (@pequiv T ==> @pequiv T ==> iff) (fun x y => x ⊑ y).
Proof.
    intros x x' [Hxx' Hx'x] y y' [Hyy' Hy'y].
    split; intros Hle.
    - apply le_trans with x; [exact (Hx'x)|].
      apply le_trans with y; [exact Hle | exact (Hyy')].
    - apply le_trans with x'; [exact (Hxx')|].
      apply le_trans with y'; [exact Hle | exact (Hy'y)].
Qed.

(*
    Properness of [⊑] with respect to [⊑] itself (flip on the left,
    forward on the right).  This is the standard "monotone substitution"
    rule used by [setoid_rewrite] inside [⊑] goals. 
*)
Global Instance le_le_proper {T : Preorder.type} :
    Proper ((fun x y => x ⊑ y) --> (fun x y => x ⊑ y) ==> impl) (fun (x y : T) => x ⊑ y).
Proof.
    intros x x' Hx y y' Hy H.
    eapply le_trans; [exact Hx|]. 
    eapply le_trans; [exact H | exact Hy].
Qed.


(* ================================================================== *)
(*   Monotone function lemmas                                         *)
(* ================================================================== *)
Section MonoFunLemmas.
(* Context {P Q R : Preorder.type}. *)

(*
    A monotone function preserves [≈]: if [x ≈ y] then [f x ≈ f y].
    This is strictly stronger than just preserving [⊑], and is the
    key fact that lets us quotient preorders by [≈] later. 
*)
Lemma mono_preserves_equiv {P Q} (f : mono_fun P Q) (x y : P) :
    x ≈ y -> f x ≈ f y.
Proof.
    intros [HxLEy HyLEx].
    split.
    - exact (mf_mono f x y HxLEy).
    - exact (mf_mono f y x HyLEx).
Qed.

(*
    Pointwise: if [f] and [g] agree on [x] up to [≈], their composites
    with any monotone [h] also agree up to [≈]. 
*)
Lemma mono_comp_equiv_r {P Q R} (h : mono_fun Q R) (f g : mono_fun P Q) :
    (forall x, f x ≈ g x) -> forall x, (mono_comp h f) x ≈ (mono_comp h g) x.
Proof.
    intros Heq x.
    simpl.
    exact (mono_preserves_equiv h (f x) (g x) (Heq x)).
Qed.

(*
    Extensionality for [mono_fun] with respect to [≈].
    If two monotone functions are pointwise [≈]-equal, they produce
    the same result when applied to any chain element. 
*)
Lemma mono_fun_ext_equiv {P Q} (f g : mono_fun P Q) (x : P) :
    (forall z, f z ≈ g z) -> f x ≈ g x.
Proof.
    intros Heq; exact (Heq x).
Qed.

End MonoFunLemmas.

(*
    [map_chain f c] and [map_chain g c] are pointwise [≈]-equivalent
    whenever [f] and [g] are pointwise [≈]-equivalent. 
*)
Lemma map_chain_ext_equiv {P Q : Preorder.type}
    (f g : mono_fun P Q) (c : chain P) :
    (forall x, f x ≈ g x) -> forall n, (map_chain f c).[n] ≈ (map_chain g c).[n].
Proof.
    intros Heq n.
    exact (Heq c.[n]).
Qed.


(* ================================================================== *)
(*   Partial order consequences                                       *)
(* ================================================================== *)
(*
    In a partial order, antisymmetry gives [x ≈ y ↔ x = y].
    This section establishes the bridge between the preorder equivalence
    [≈] and propositional equality [=], which is the key fact that makes
    the sup operator well-behaved (used extensively in [CPOTheory.v]). 
*)
Section PartialOrderLemmas.
Context {T : PartialOrder.type}.

(*
    The main bridge lemma: [≈] collapses to [=] in a partial order.
    We state both directions for ease of use. 
*)
Lemma pequiv_iff_eq (x y : T) : x ≈ y <-> x = y.
Proof.
    split.
    - intros [HxLEy HyLEx].
      exact (le_antisym _ _ HxLEy HyLEx).
    - intros ->.
      exact (pequiv_refl y).
Qed.

(* Convenient directed corollaries. *)
Corollary pequiv_eq (x y : T) : x ≈ y -> x = y.
Proof.
    intros H; exact (proj1 (pequiv_iff_eq x y) H).
Qed.

Corollary eq_pequiv (x y : T) : x = y -> x ≈ y.
Proof.
    intros ->; exact (pequiv_refl y).
Qed.

(*
    Equality implies [⊑] in both directions.  This seems obvious but
    is needed in proofs where the hypothesis is [x = y] rather than
    [x ⊑ y]. 
*)
Lemma eq_le (x y : T) : x = y -> x ⊑ y.
Proof.
    intros ->; apply (le_refl y).
Qed.

Lemma eq_ge (x y : T) : x = y -> y ⊑ x.
Proof.
  intros ->; apply (le_refl y).
Qed.

(*
    Uniqueness of least upper bounds (or any pair of elements that are
    each below the other). 
*)
Lemma le_antisym_unique (x y : T) : x ⊑ y -> y ⊑ x -> x = y.
Proof.
    exact (le_antisym x y).
Qed.

(*
    If [x ⊑ y] and [x = y] then both are redundant — [y ⊑ x] is free. 
*)
Lemma le_eq_ge (x y : T) : x ⊑ y -> x = y -> y ⊑ x.
Proof.
  intros _ ->; apply (le_refl y).
Qed.

(*
    Strict inequality: if [x ⊑ y] but [x ≠ y] then [¬ (y ⊑ x)].
    This is the contrapositive of antisymmetry. 
*)
Lemma le_ne_not_ge (x y : T) : x ⊑ y -> x <> y -> ~ (y ⊑ x).
Proof.
    intros Hle Hne Hge.
    exact (Hne (le_antisym _ _ Hle Hge)).
Qed.

End PartialOrderLemmas.

(*
    [⊑] is antisymmetric in any partial order (registered as a Proper
    instance so that [rewrite] with [=] works under [⊑]). 
*)
Global Instance le_eq_proper {T : PartialOrder.type} :
    Proper (@eq T ==> @eq T ==> iff) (fun x y => x ⊑ y).
Proof.
    intros x x' -> y y' ->.
    reflexivity.
Qed.


(* ================================================================== *)
(*   Chain index lemmas                                               *)
(* ================================================================== *)
(*
    These lemmas expose the monotonicity of chains through standard
    natural-number arithmetic.  They exist so that downstream proofs
    can avoid spelling out Nat lemma names when reasoning about chain
    elements.

    Heavier chain constructions (eventually-constant chains, chain
    comparisons across a CPO) belong in [ChainTheory.v]. 
*)

Section ChainIndexLemmas.
Context {P : Preorder.type}.

(*
    Alias for [ch_mono] with the same argument order, for cases where
    callers prefer a named lemma to the field projection. 
*)
Lemma chain_mono_le (c : chain P) {m n : nat} (H : m <= n) :
    c.[m] ⊑ c.[n]. 
Proof.
    exact (ch_mono c m n H).
Qed.

(*
    Transitivity through a pivot index: if [m ≤ k ≤ n] then
    [c.[m] ⊑ c.[n]] via [c.[k]]. 
*)
Lemma chain_le_trans (c : chain P) {m k n : nat} :
    m <= k -> k <= n -> c.[m] ⊑ c.[n].
Proof.
    intros HmLEk HkLEn.
    apply ch_mono.
    exact (Nat.le_trans _ _ _ HmLEk HkLEn).
Qed.

(*
    The first element of a chain is below every other element. 
*)
Lemma chain_zero_le (c : chain P) (n : nat) : c.[0] ⊑ c.[n].
Proof.
    apply ch_mono.
    exact (Nat.le_0_l n).
Qed.

(*
    An element is below the element [k] steps later. 
*)
Lemma chain_le_add (c : chain P) (n k : nat) : c.[n] ⊑ c.[n + k].
Proof.
    apply ch_mono.
    exact (Nat.le_add_r n k).
Qed.

Lemma chain_le_add_l (c : chain P) (n k : nat) : c.[n] ⊑ c.[k + n].
Proof.
    apply ch_mono.
    exact (Nat.le_add_l n k).
Qed.

(*
    The tail chain simply shifts the index by one.
    ([tail_chain_index] is definitional; proved by [reflexivity].) 
*)
Lemma tail_chain_index (c : chain P) (n : nat) :
    (tail_chain c).[n] = c.[S n].
Proof.
    reflexivity.
Qed.

(*
    Each element of the original chain is below the corresponding
    element of the tail chain (the tail has moved one step forward). 
*)
Lemma tail_chain_ge (c : chain P) (n : nat) :
    c.[n] ⊑ (tail_chain c).[n].
Proof.
    rewrite tail_chain_index.
    exact (chain_succ_le c n).
Qed.

(*
    The tail chain is itself above the original chain at every index
    in the other direction: elements of the tail at index [n] come
    from index [S n] of [c], so they are higher. 
*)
Lemma tail_chain_mono_index (c : chain P) {m n : nat} (H : m <= n) :
    (tail_chain c).[m] ⊑ (tail_chain c).[n].
Proof.
    exact (ch_mono (tail_chain c) _ _ H).
Qed.

(*
    Constant chain: all elements are equal to the basepoint. 
*)
Lemma const_chain_index (x : P) (n : nat) :
    (const_chain x).[n] = x.
Proof.
    reflexivity.
Qed.

(*
    Applying a monotone function to a constant chain gives a constant
    chain (elementwise). 
*)
Lemma map_const_chain {Q : Preorder.type} (f : mono_fun P Q) (x : P) (n : nat) :
    (map_chain f (const_chain x)).[n] = f x.
Proof.
    reflexivity.
Qed.

(*
    If two chains are pointwise equal (as elements of [P]) then they
    are pointwise [≈]-equivalent. 
*)
Lemma chain_ext_equiv (c d : chain P) :
    (forall n, c.[n] = d.[n]) -> forall n, c.[n] ≈ d.[n].
Proof.
    intros Heq n.
    rewrite Heq.
    exact (pequiv_refl (d.[n])).
Qed.

(*
    Pointwise [⊑] between two chains, spelled out for convenience. 
*)
Lemma chain_le_pointwise (c d : chain P) :
    (forall n, c.[n] ⊑ d.[n]) -> forall n, c.[n] ⊑ d.[n].
Proof.
    intros H; exact H.
Qed.

(*
    Interleaving: the max of two nat indices gives a common upper bound
    in any chain, i.e. both [c.[m]] and [c.[n]] are below [c.[max m n]]. 
*)
Lemma chain_le_max_l (c : chain P) (m n : nat) :
    c.[m] ⊑ c.[Nat.max m n].
Proof.
    apply ch_mono.
    exact (Nat.le_max_l m n).
Qed.

Lemma chain_le_max_r (c : chain P) (m n : nat) :
    c.[n] ⊑ c.[Nat.max m n].
Proof.
    apply ch_mono.
    exact (Nat.le_max_r m n).
Qed.

End ChainIndexLemmas.


(* ================================================================== *)
(*   [map_chain] lemmas                                               *)
(* ================================================================== *)

Section MapChainLemmas.
Context {P Q R : Preorder.type}.

(*
    [map_chain] distributes over composition of monotone functions. 
*)
Lemma map_chain_comp (g : mono_fun Q R) (f : mono_fun P Q) (c : chain P) (n : nat) :
    (map_chain (mono_comp g f) c).[n] = (map_chain g (map_chain f c)).[n].
Proof.
    reflexivity.
Qed.

(*
    [map_chain] with the identity is the identity on chains (pointwise). 
*)
Lemma map_chain_id (c : chain P) (n : nat) :
    (map_chain (mono_id P) c).[n] = c.[n].
Proof.
    reflexivity.
Qed.

(*
    [map_chain f] distributes over [tail_chain]. 
*)
Lemma map_chain_tail (f : mono_fun P Q) (c : chain P) (n : nat) :
    (map_chain f (tail_chain c)).[n] = (tail_chain (map_chain f c)).[n].
Proof.
    reflexivity.
Qed.

(*
    Pointwise monotonicity of [map_chain]:
    if [c.[n] ⊑ d.[n]] for all [n] then the mapped chains are also
    pointwise ordered. 
*)
Lemma map_chain_le {f : mono_fun P Q} (c d : chain P):
    (forall n, c.[n] ⊑ d.[n]) -> forall n, (map_chain f c).[n] ⊑ (map_chain f d).[n].
Proof.
    intros Hle n.
    exact (mf_mono f (c.[n]) (d.[n]) (Hle n)).
Qed.

End MapChainLemmas.