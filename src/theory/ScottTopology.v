(*  ScottTopology

    Phase 0: The way-below relation and the Scott topology on omega-CPOs.

    This is [src/theory/ScottTopology.v].

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, PointedCPO, continuous
      [src/structures/Morphisms.v] — cont_fun
      [src/theory/OrderTheory.v]   — le_antisym, smalloid instances
      [src/theory/ChainTheory.v]   — chain_shift, chain_shift_index
      [src/theory/CPOTheory.v]     — sup_least, sup_upper, sup_const_chain,
                                     mono_sup_le, continuous_of_le

    ω-CPO vs DCPO note
    ==================
    This library works with ω-CPOs throughout, so every notion here uses
    ω-chains (monotone sequences indexed by ℕ) rather than arbitrary
    directed sets.  Concretely:

    - [x ≪ y] means: for every ω-chain [c], if [y ⊑ ⊔ c] then [∃ n, x ⊑ c.[n]].
    - A set is Scott-open if it is upward-closed and inaccessible by ω-chain sups.

    In a general dcpo these notions use directed sets.  The two coincide on
    ω-algebraic domains (where every element is the ω-chain sup of compact
    elements below it), which covers all domains arising in programming-language
    semantics within Phase 0–2 of this project.

    Scope note on way-below under continuous maps
    =============================================
    Continuous maps do NOT preserve ≪ in general ω-CPOs.  To show [f x ≪ f y]
    from [x ≪ y] and continuity of [f], one would need: for any chain [c] in
    the *codomain* with [f y ⊑ ⊔ c], a witness [n] with [f x ⊑ c.[n]].  But
    [x ≪ y] only yields witnesses in chains in the *domain*; there is no way
    to pull a codomain chain back through [f] without additional structure (e.g.
    [f] being an order-embedding, or the domain being a continuous domain).
    The preservation of ≪ under continuous maps therefore does not appear here.

    Contents:
    - §1  Way-below relation — [waybelow], notation [x ≪ y]
    - §2  Scott topology — [scott_open], closure properties
    - §3  Complement of a principal downset is Scott-open (key auxiliary)
    - §4  Algebraic ↔ topological Scott-continuity equivalence

    Phase coverage:
      Phase 0 — all sections
      Phase 1 — §4 used when verifying enriched-category continuity conditions
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory ChainTheory CPOTheory.

From Stdlib Require Import Classical.


(* ================================================================== *)
(** §1  Way-below relation                                             *)
(* ================================================================== *)
(*
    [x ≪ y] (read: "x is way-below y", or "x is a finite approximation to y")
    means that any ω-chain that reaches [y] has already reached [x] at some
    finite stage.
*)

Definition waybelow {D : CPO.type} (x y : D) : Prop :=
  forall (c : chain D), y ⊑ ⊔ c -> exists n : nat, x ⊑ c.[n].

Notation "x ≪ y" := (waybelow x y) (at level 70, no associativity).
Notation "x ≪[ D ] y" := (@waybelow D x y)
  (at level 70, no associativity, only parsing).

Section WayBelowLemmas.
Context {D : CPO.type}.

(*
    Way-below implies below.
    Use the constant chain at [y]: its sup is [y], so [x ≪ y] gives [n]
    with [x ⊑ (const_chain y).[n] = y]. 
*)
Lemma waybelow_le (x y : D) : x ≪ y -> x ⊑ y.
Proof.
    intros Hwb.
    destruct (Hwb (const_chain y)) as [n Hn].
    - rewrite (sup_const_chain y); apply (@le_refl D).
    - rewrite const_chain_index in Hn; exact Hn.
Qed.

(*
    Way-below is transitive.
    Given [x ≪ y ≪ z] and chain [c] with [z ⊑ ⊔ c]:
    (1) By [y ≪ z]: get [n] with [y ⊑ c.[n]].
    (2) Shift: [y ⊑ c.[n] = (chain_shift n c).[0] ⊑ ⊔ (chain_shift n c)].
    (3) By [x ≪ y]: get [m] with [x ⊑ (chain_shift n c).[m] = c.[m + n]].
    (4) Witness [m + n] in [c]. 
*)
Lemma waybelow_trans (x y z : D) : x ≪ y -> y ≪ z -> x ≪ z.
Proof.
    intros Hxy Hyz c Hzc.
    destruct (Hyz c Hzc) as [n Hyn].
    destruct (Hxy (chain_shift n c)) as [m Hm].
    - apply (le_trans _ (⊔ c) _).
        + apply (le_trans _ (c.[n]) _); [exact Hyn|].
          apply sup_upper.
        + apply sup_mono; intros k.
          apply chain_shift_ge.
    - rewrite chain_shift_index in Hm.
      exists (m + n); exact Hm.
Qed.

(*
    Way-below is upward-closed on the right:
    [x ≪ y] and [y ⊑ z] imply [x ≪ z]. 
*)
Lemma waybelow_le_r (x y z : D) : x ≪ y -> y ⊑ z -> x ≪ z.
Proof.
    intros Hwb Hyz c Hzc.
    exact (Hwb c (le_trans _ _ _ Hyz Hzc)).
Qed.

(*
    Way-below is downward-closed on the left:
    [w ⊑ x] and [x ≪ y] imply [w ≪ y]. 
*)
Lemma le_waybelow_l (w x y : D) : w ⊑ x -> x ≪ y -> w ≪ y.
Proof.
    intros Hwx Hxy c Hyc.
    destruct (Hxy c Hyc) as [n Hn].
    exact (ex_intro _ n (le_trans _ _ _ Hwx Hn)).
Qed.

(*
    Combined monotonicity: [a ⊑ x ≪ y ⊑ b] implies [a ≪ b]. 
*)
Lemma waybelow_mono (a x y b : D) :
    a ⊑ x -> x ≪ y -> y ⊑ b -> a ≪ b.
Proof.
    intros Hax Hxy Hyb.
    exact (le_waybelow_l a x b Hax (waybelow_le_r x y b Hxy Hyb)).
Qed.

(*
    An element way-below the sup of a chain has a finite witness in that chain.
    (This is just the definition, named for clarity.) 
*)
Lemma waybelow_chain_witness (x y : D) (c : chain D) :
    x ≪ y -> y ⊑ ⊔ c -> exists n, x ⊑ c.[n].
Proof.
    intros Hwb Hyc; exact (Hwb c Hyc).
Qed.

(*
    If [x ≪ c.[k]] for some element of the chain, then [x ≪ ⊔ c]. 
*)
Lemma waybelow_elem_to_sup (x : D) (c : chain D) (k : nat) :
    x ≪ c.[k] -> x ≪ ⊔ c.
Proof.
    intros Hwb.
    exact (waybelow_le_r x (c.[k]) (⊔ c) Hwb (sup_upper c k)).
Qed.

End WayBelowLemmas.

(*
    In a pointed CPO, [⊥] is way-below every element.
    For any chain [c] with [x ⊑ ⊔ c], witness [n = 0]:
    [⊥ ⊑ c.[0]] by [bottom_least]. 
*)
Lemma waybelow_bottom {D : PointedCPO.type} (x : D) : (⊥ : D) ≪ x.
Proof.
    intros c _.
    exists 0. exact (bottom_least (c.[0])).
Qed.

(*
    A _compact_ element is one that is way-below itself.
    Equivalently: [x] is compact if any chain reaching [x] has already
    reached [x] at a finite stage. 
*)
Definition compact {D : CPO.type} (x : D) : Prop := x ≪ x.

(*
    A compact element below the sup of a chain has a finite witness. 
*)
Lemma compact_le_sup {D : CPO.type} (x : D) (c : chain D) :
    compact x -> x ⊑ ⊔ c -> exists n, x ⊑ c.[n].
Proof.
    intros Hcomp Hle; exact (Hcomp c Hle).
Qed.

(*
    [⊥] is compact in any pointed CPO. 
*)
Lemma bottom_compact {D : PointedCPO.type} : compact (⊥ : D).
Proof.
  exact (waybelow_bottom ⊥).
Qed.


(* ================================================================== *)
(*   Scott topology                                                   *)
(* ================================================================== *)
(*
    A subset [U : D → Prop] is _Scott-open_ when:
    (1) It is upward-closed: [x ∈ U] and [x ⊑ y] implies [y ∈ U].
    (2) It is inaccessible by ω-chain sups: [⊔ c ∈ U] implies [∃ n, c.[n] ∈ U].

    Condition (2) captures the finitary character of Scott-open sets:
    a chain can only "reach" an open set at a finite step. 
*)

Definition scott_open {D : CPO.type} (U : D -> Prop) : Prop :=
  (forall x y : D, U x -> x ⊑ y -> U y) /\
  (forall c : chain D, U (⊔ c) -> exists n, U (c.[n])).

Section ScottOpenLemmas.
Context {D : CPO.type}.

(** Extract upward-closure from [scott_open]. *)
Lemma scott_open_up {U : D -> Prop} (Hso : scott_open U) :
    forall x y, U x -> x ⊑ y -> U y.
Proof.
    exact (proj1 Hso).
Qed.

(** Extract inaccessibility from [scott_open]. *)
Lemma scott_open_inac {U : D -> Prop} (Hso : scott_open U) :
    forall c : chain D, U (⊔ c) -> exists n, U (c.[n]).
Proof.
    exact (proj2 Hso).
Qed.

(** The full set [D] is Scott-open. *)
Lemma scott_open_univ : scott_open (fun _ : D => True).
Proof.
    split.
    - intros _ _ H _. exact H.
    - intros _ H. exact (ex_intro _ 0 H).
Qed.

(** The empty set is Scott-open. *)
Lemma scott_open_empty : scott_open (fun _ : D => False).
Proof.
    split.
    - intros _ _ H _. exact H.
    - intros _ H. exact (False_ind _ H).
Qed.

(*
    Binary intersections of Scott-open sets are Scott-open.
    For inaccessibility: if [⊔ c ∈ U ∩ V], get witnesses [n] (for U) and
    [m] (for V), then [Nat.max n m] works for both by upward-closure. 
*)
Lemma scott_open_inter (U V : D -> Prop) :
    scott_open U -> scott_open V ->
    scott_open (fun x => U x /\ V x).
Proof.
    intros [HUup HUin] [HVup HVin].
    split.
    - intros x y [HUx HVx] Hxy.
      split.
      + exact (HUup x y HUx Hxy).
      + exact (HVup x y HVx Hxy).
    - intros c [HUc HVc].
      destruct (HUin c HUc) as [n HUn].
      destruct (HVin c HVc) as [m HVm].
      exists (Nat.max n m).
      split.
      + apply HUup with (x := c.[n]); [exact HUn|].
        apply (@ch_mono).
        exact (PeanoNat.Nat.le_max_l n m).
      + apply HVup with (x := c.[m]); [exact HVm|].
        apply (@ch_mono).
        exact (PeanoNat.Nat.le_max_r n m).
Qed.

(*
    Arbitrary unions of Scott-open sets are Scott-open. 
*)
Lemma scott_open_union {I : Type} (F : I -> D -> Prop) :
    (forall i, scott_open (F i)) ->
    scott_open (fun x => exists i, F i x).
Proof.
    intros HF.
    split.
    - intros x y [i Hi] Hxy.
      exists i.
      exact (scott_open_up (HF i) x y Hi Hxy).
    - intros c [i Hic].
      destruct (scott_open_inac (HF i) c Hic) as [n Hn].
      exists n, i. exact Hn.
Qed.

End ScottOpenLemmas.


(* ================================================================== *)
(*   Complement of a principal downset is Scott-open                  *)
(* ================================================================== *)
(*
    For any [x : D], the set [{z | ¬(z ⊑ x)}] (everything strictly
    incomparable-or-above [x], i.e. the complement of the principal
    downset [↓x]) is Scott-open.

    This is the key auxiliary lemma for the equivalence theorem:
    it lets us encode "not below [x]" as membership in a Scott-open set,
    turning algebraic inequalities into topological arguments.

    Upward-closure: If [¬(z ⊑ x)] and [z ⊑ w], then [¬(w ⊑ x)], because
    otherwise [z ⊑ w ⊑ x] contradicts [¬(z ⊑ x)].

    Inaccessibility: If [¬(⊔ c ⊑ x)], then some [c.[n] ⊑ x] fails.
    Proof by contrapositive: if all [c.[n] ⊑ x], then [⊔ c ⊑ x] by
    [sup_least], contradicting the hypothesis.  The quantifier flip
    ([¬ ∀] to [∃ ¬]) uses classical logic. 
*)
Lemma complement_downset_scott_open {D : CPO.type} (x : D) :
    scott_open (fun z => ~ z ⊑ x).
Proof.
    split.
    - intros z w Hnzx Hzw Hwx.
      exact (Hnzx (le_trans z w x Hzw Hwx)).
    - intros c Hnc.
      apply NNPP; intros Hno.
      apply Hnc.
      apply sup_least; intros n.
      apply NNPP; intros Hnn.
      apply Hno; exists n.
      exact Hnn.
Qed.

(* ================================================================== *)
(*   Algebraic ↔ topological Scott-continuity                         *)
(* ================================================================== *)
(*
    A function [f : D → E] is _topologically Scott-continuous_ if
    preimages of Scott-open sets are Scott-open:
      [scott_continuous f  ↔  ∀ U, scott_open U → scott_open (f⁻¹(U))]

    The main theorem of this section establishes the equivalence with the
    algebraic definition [continuous f] (from [CPO.v]):
      [f (⊔ c) = ⊔ (map_chain f c)]  for all ω-chains [c].

    We prove this in three steps:

    (A) Algebraic [continuous f] → topological [scott_continuous f]:
        straightforward from the definitions of continuity and Scott-openness.

    (B) Topological → monotone: uses [complement_downset_scott_open] to turn
        "not monotone" into a contradiction.

    (C) Topological → algebraic: uses [complement_downset_scott_open] applied
        to [⊔ (map_chain f c)] to turn "not continuous" into a contradiction.
*)

(*
    Topological Scott-continuity as a predicate on functions. 
*)
Definition scott_continuous {D E : CPO.type} (f : D -> E) : Prop :=
  forall (U : E -> Prop), scott_open U -> scott_open (fun x => U (f x)).

Section ScottContinuityEquivalence.
Context {D E : CPO.type}.

(* ------------------------------------------------------------------ *)
(*  (A) Algebraic → topological                                        *)
(* ------------------------------------------------------------------ *)
(*
    A monotone, algebraically continuous function is topologically
    Scott-continuous.

    Upward-closure of [f⁻¹(U)]: if [U(f x)] and [x ⊑ y], then [f x ⊑ f y]
    (monotone), so [U(f y)] (U is upward-closed).

    Inaccessibility of [f⁻¹(U)]: if [U(f(⊔ c))], rewrite [f(⊔ c)] as
    [⊔(map_chain f c)] by continuity; then inaccessibility of [U] gives
    [n] with [U((map_chain f c).[n])] = [U(f(c.[n]))]. 
*)
Lemma cont_imp_scott_continuous (f : mono_fun D E) (Hcont : continuous f) :
    scott_continuous f.
Proof.
    intros U [HUup HUin].
    split.
    - intros x y HUfx Hxy.
      exact (HUup (f x) (f y) HUfx (mf_mono f x y Hxy)).
    - intros c HUfc.
      rewrite Hcont in HUfc.
      exact (HUin (map_chain f c) HUfc).
Qed.

Lemma cont_fun_scott_continuous (f : [D →c E]) : scott_continuous f.
Proof.
    exact (cont_imp_scott_continuous (cf_mono f) (cf_cont f)).
Qed.


(* ------------------------------------------------------------------ *)
(*  (B) Topological → monotone                                         *)
(* ------------------------------------------------------------------ *)
(*
    A topologically Scott-continuous function is monotone.

    Suppose [x ⊑ y] but [¬(f x ⊑ f y)].  The set [U = {z | ¬(z ⊑ f y)}]
    is Scott-open.  The preimage [f⁻¹(U)] is Scott-open by [Hsc], and is
    upward-closed.  Since [f x ∈ U], we have [x ∈ f⁻¹(U)].  Upward-closure
    and [x ⊑ y] give [y ∈ f⁻¹(U)], i.e. [¬(f y ⊑ f y)].  But [f y ⊑ f y]
    by [le_refl].  Contradiction. 
*)
Lemma scott_continuous_mono (f : D -> E) (Hsc : scott_continuous f) :
    monotone D E f.
Proof.
    intros x y Hxy.
    apply NNPP; intros Hnfxy.
    set (U := fun z : E => ~ z ⊑ f y).
    assert (HUso : scott_open U).
    - exact (complement_downset_scott_open (f y)).
    - assert (HpUso : scott_open (fun z => U (f z))) by exact (Hsc U HUso).
      assert (HUfy : U (f y)) by exact (scott_open_up HpUso x y Hnfxy Hxy).
      exact (HUfy (le_refl (f y))).
Qed.


(* ------------------------------------------------------------------ *)
(*  (C) Topological → algebraic (for a mono_fun)                      *)
(* ------------------------------------------------------------------ *)
(*
    If [f : mono_fun D E] is topologically Scott-continuous, then it is
    algebraically continuous: [f(⊔ c) = ⊔(map_chain f c)].

    Proof via [continuous_of_le]: it suffices to show [f(⊔ c) ⊑ ⊔(map_chain f c)].
    The reverse direction [⊔(map_chain f c) ⊑ f(⊔ c)] follows from monotonicity
    alone (this is [mono_sup_le] in CPOTheory.v).

    For [f(⊔ c) ⊑ ⊔(map_chain f c)]: suppose for contradiction that
    [¬(f(⊔ c) ⊑ ⊔(map_chain f c))].  The set [U = {z | ¬(z ⊑ ⊔(map_chain f c))}]
    is Scott-open.  The preimage [f⁻¹(U)] is Scott-open.  Since [⊔ c ∈ f⁻¹(U)],
    inaccessibility gives [n] with [c.[n] ∈ f⁻¹(U)], i.e.
    [¬(f(c.[n]) ⊑ ⊔(map_chain f c))].  But [f(c.[n]) = (map_chain f c).[n] ⊑ ⊔(map_chain f c)]
    by [sup_upper].  Contradiction. 
*)
Lemma scott_continuous_of_continuous (f : mono_fun D E)
    (Hsc : scott_continuous f) : continuous f.
Proof.
    apply continuous_of_le; intros c.
    apply NNPP; intros Hn.
    set (U := fun z : E => ~ z ⊑ ⊔ (map_chain f c)).
    assert (HUso : scott_open U).
    - exact (complement_downset_scott_open (⊔ (map_chain f c))).
    - assert (HpUso : scott_open (fun z => U (f z))) by exact (Hsc U HUso).
      destruct (scott_open_inac HpUso c Hn) as [n Hn'].
      exact (Hn' (sup_upper (map_chain f c) n)).
Qed.


(* ------------------------------------------------------------------ *)
(*  Main equivalence theorem                                           *)
(* ------------------------------------------------------------------ *)
(*
    For a [mono_fun], algebraic and topological Scott-continuity coincide. 
*)
Theorem continuous_iff_scott_continuous (f : mono_fun D E) :
    continuous f <-> scott_continuous f.
Proof.
    split.
    - exact (cont_imp_scott_continuous f).
    - exact (scott_continuous_of_continuous f).
Qed.

(*
    Packaging topological continuity into a [cont_fun]:
    a topologically Scott-continuous plain function gives rise to a [cont_fun]. 
*)
Lemma scott_continuous_to_cont_fun (f : D -> E) (Hsc : scott_continuous f) :
    [D →c E].
Proof.
  exact (Build_cont_fun
           (Build_mono_fun f (scott_continuous_mono f Hsc))
           (scott_continuous_of_continuous
              (Build_mono_fun f (scott_continuous_mono f Hsc))
              Hsc)).
Qed.


(* ------------------------------------------------------------------ *)
(*  Corollaries                                                         *)
(* ------------------------------------------------------------------ *)

(*
    The preimage of a Scott-open set under a continuous function is Scott-open. 
*)
Lemma cont_preimage_scott_open (f : [D →c E]) (U : E -> Prop) :
    scott_open U -> scott_open (fun x => U (f x)).
Proof.
    intros HU.
    exact (cont_fun_scott_continuous f U HU).
Qed.

(*
    Composition of topologically Scott-continuous functions is
    topologically Scott-continuous. 
*)
Lemma scott_continuous_comp {F : CPO.type} (g : F -> E) (f : D -> F) :
    scott_continuous g -> scott_continuous f ->
    scott_continuous (fun x => g (f x)).
Proof.
    intros Hg Hf U HU.
    exact (Hf (fun z => U (g z)) (Hg U HU)).
Qed.

(*
    The identity function is topologically Scott-continuous. 
*)
Lemma scott_continuous_id : @scott_continuous D D (fun x : D => x).
Proof.
    intros U HU.
    exact HU.
Qed.

End ScottContinuityEquivalence.