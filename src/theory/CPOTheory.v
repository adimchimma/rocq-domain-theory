(*  CPOTheory

    Phase 0: Derived theory for omega-complete partial orders.

    This is [src/theory/CPOTheory.v].

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, PointedCPO, HasSup, IsCPO, continuous
      [src/structures/Morphisms.v] — cont_fun, strict_fun
      [src/theory/OrderTheory.v]   — pequiv_eq, eq_le, setoid instances
      [src/theory/ChainTheory.v]   — chain_shift, eventually_const, coherent_family

    Note on [sup_mono] and [sup_ext]:
      These two lemmas are proved in [CPO.v] (because they are used in the
      definition of [continuous] and needed immediately by [Morphisms.v]).
      They are re-exported here so that downstream files can import a single
      [CPOTheory] module and get the full suite of sup lemmas.

    Contents:
    - §1  Sup characterisation — uniqueness, constant/tail/shift chains, eventually-const
    - §2  Sup and [map_chain] — monotone functions, sup of composed chains
    - §3  Scott continuity — [continuous_of_le], [cont_fun_ext], equivalent forms
    - §4  Admissible predicates and chain Scott induction
    - §5  PointedCPO consequences — [⊥] and sup

    Phase coverage:
      Phase 0 — all sections
      Phase 1 — §4 (admissibility) re-used in enriched setting

    References:
      Benton, Kennedy & Varming (2009) §2 — continuous functions, admissibility.
      Abramsky & Jung (1994) §2.1–2.2 — CPO theory, sup lemmas.
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory ChainTheory.

From Stdlib Require Import FunctionalExtensionality ProofIrrelevance.
From Stdlib Require Import PeanoNat.

(*
    [sup_mono] and [sup_ext] are proved in [CPO.v] and are available to any
    file that imports [CPO].  They are not re-proved here.

      sup_mono : (forall n, c.[n] ⊑ d.[n]) -> ⊔ c ⊑ ⊔ d
      sup_ext  : (forall n, c.[n] = d.[n])  -> ⊔ c = ⊔ d
*)


(* ================================================================== *)
(*   Sup characterisation lemmas                                      *)
(* ================================================================== *)

Section SupLemmas.
Context {D : CPO.type}.

(*
    Uniqueness of least upper bounds.
    If [s] is an upper bound of [c] with [s ⊑ ⊔ c], then [s = ⊔ c].
    More generally: two elements that are each ⊑ the sup of the other's
    chain are equal.  We prove the direct form: uniqueness of the sup. 
*)
Lemma sup_unique (c : chain D) (s : D) :
    (forall n, c.[n] ⊑ s) -> s ⊑ ⊔ c -> s = ⊔ c.
Proof.
    intros Hub Hle.
    apply le_antisym.
    - exact Hle.
    - exact (sup_least c s Hub).
Qed.

(*
    [⊔ c ⊑ x] if and only if [x] is an upper bound of [c].
    This rephrases [sup_least] as an iff, which often reads more naturally
    when the goal is [⊔ c ⊑ x]. 
*)
Lemma sup_le_iff (c : chain D) (x : D) :
    ⊔ c ⊑ x <-> forall n, c.[n] ⊑ x.
Proof.
    split.
    - intros Hup n.
      apply le_trans with (⊔ c).
      + apply sup_upper.
      + exact Hup.
    - intros Hup.
      exact (sup_least c x Hup).
Qed.

(*
    [x ⊑ ⊔ c] if [x ⊑ c.[n]] for some [n].
    The converse does not hold in general (the sup may be strictly above
    every element of a non-constant chain). 
*)
Lemma le_sup_of_le_elem (c : chain D) (x : D) (n : nat) :
    x ⊑ c.[n] -> x ⊑ ⊔ c.
Proof.
    intros Hle.
    apply (@le_trans D) with (c.[n]).
    - exact Hle.
    - exact (sup_upper c n).
Qed.

(*
    The sup of a constant chain is the constant value. 
*)
Lemma sup_const_chain (x : D) : ⊔ (const_chain x) = x.
Proof.
    apply le_antisym.
    - apply sup_least.
      intro n.
      apply le_refl.
    - exact (@sup_upper D (const_chain x) 0).
Qed.

(*
    The sup of the tail chain equals the sup of the original chain.
    Proof sketch:
      [⊔ c ⊑ ⊔ (tail_chain c)]: each [c.[n] ⊑ c.[S n] ⊑ ⊔ (tail_chain c)]
      [⊔ (tail_chain c) ⊑ ⊔ c]: each [(tail_chain c).[n] = c.[S n] ⊑ ⊔ c]
*)
Lemma sup_tail (c : chain D) : ⊔ (tail_chain c) = ⊔ c.
Proof.
    apply le_antisym.
    - apply sup_least.
      intro n; rewrite tail_chain_index.
      exact (sup_upper c (S n)).
    - apply sup_least; intros n.
      exact (le_trans _ _ _ (chain_succ_le c n) (sup_upper (tail_chain c) n)).
Qed.

(*
    The sup of [chain_shift k c] equals the sup of [c].
    Proof sketch:
      [⊔ c ⊑ ⊔ (chain_shift k c)]: [c.[n] ⊑ c.[n+k] = (chain_shift k c).[n] ⊑ ⊔ ...]
      [⊔ (chain_shift k c) ⊑ ⊔ c]: [(chain_shift k c).[n] = c.[n+k] ⊑ ⊔ c]
*)
Lemma sup_shift (k : nat) (c : chain D) : ⊔ (chain_shift k c) = ⊔ c.
Proof.
    apply le_antisym.
    - apply sup_least.
      intros n; rewrite chain_shift_index.
      apply sup_upper.
    - apply sup_least; intros n.
      apply (le_trans _ ((chain_shift k c).[n]) _).
      + apply chain_shift_ge.
      + apply sup_upper.
Qed.

(*
    The sup of an eventually-constant chain equals its limit value.
    This is the key lemma used in [Sums.v] after establishing that
    the chain eventually lands in one summand.

    Proof:
      [⊔ c ⊑ x]: for any n, if n < N then c.[n] ⊑ c.[N] = x; if n ≥ N then c.[n] = x ⊑ x.
                  Either way c.[n] ⊑ x, so by sup_least, ⊔ c ⊑ x.
      [x ⊑ ⊔ c]: x = c.[N] ⊑ ⊔ c by sup_upper.
*)
Lemma sup_eventually_const (c : chain D) (x : D) :
    eventually_const c x -> ⊔ c = x.
Proof.
    intros [N HN].
    apply le_antisym.
    - apply sup_least; intros n.
      destruct (Compare_dec.le_gt_dec N n) as [HNn | HnN].
      + rewrite HN; [apply le_refl | exact HNn]. 
      + apply (le_trans _ (c.[N]) _).
        * apply ch_mono. apply Nat.lt_le_incl.
          exact HnN.
        * rewrite (HN N (Nat.le_refl N)); apply le_refl.
    - rewrite <- (HN N (Nat.le_refl N)). apply sup_upper.
Qed.

(*
    Two chains that are pointwise [≈]-equivalent have the same sup.
    This is [sup_ext] generalised from [=] to [≈], reduced to [sup_ext]
    via [pequiv_eq]. 
*)
Lemma sup_equiv (c d : chain D) :
    (forall n, c.[n] ≈ d.[n]) -> ⊔ c = ⊔ d.
Proof.
    intros Heq.
    apply sup_ext.
    intros n.
    apply pequiv_eq.
    exact (Heq n).
Qed.

(*
    Monotonicity of sup in a weaker pointwise sense:
    if each element of [c] is ⊑ some element of [d] (not necessarily
    at the same index), then [⊔ c ⊑ ⊔ d]. 
*)
Lemma sup_le_of_pointwise_ex (c d : chain D) :
    (forall n, exists m, c.[n] ⊑ d.[m]) -> ⊔ c ⊑ ⊔ d.
Proof.
    intros H.
    apply sup_least; intros n.
    destruct (H n) as [m Hm].
    apply (le_trans _ (d.[m]) _).
    - exact Hm.
    - apply sup_upper.
Qed.

End SupLemmas.


(* ================================================================== *)
(*   Sup and [map_chain]                                              *)
(* ================================================================== *)

Section SupMapChain.

(*
    The sup of the identity-mapped chain equals the original sup.
    ([map_chain (mono_id D) c] is pointwise equal to [c] by [map_chain_id].) 
*)
Lemma sup_map_chain_id {D : CPO.type} (c : chain D) :
    ⊔ (map_chain (mono_id D) c) = ⊔ c.
Proof.
    apply sup_ext.
    apply map_chain_id.
Qed.

(*
    Sup of a composed [map_chain] equals the sup of the iterated application.
*)
Lemma sup_map_chain_comp {D E F : CPO.type}
    (g : mono_fun E F) (f : mono_fun D E) (c : chain D) :
    ⊔ (map_chain (mono_comp g f) c) = ⊔ (map_chain g (map_chain f c)).
Proof.
    apply sup_ext; intros n.
    apply map_chain_comp.
Qed.

(*
    For any _monotone_ function [f], the sup of the image chain is always
    ⊑ the image of the sup:
      [⊔ (map_chain f c) ⊑ f (⊔ c)]
    Proof: each [f (c.[n]) ⊑ f (⊔ c)] by monotonicity + [sup_upper]. 

    This direction is "free" from monotonicity alone.  Scott continuity
    is the statement that equality holds. 
*)
Lemma mono_sup_le {D E : CPO.type} (f : mono_fun D E) (c : chain D) :
    ⊔ (map_chain f c) ⊑ f (⊔ c).
Proof.
    apply sup_least; intros n.
    apply mf_mono.
    apply sup_upper.
Qed.

(*
    For a _continuous_ function, the inequality is an equality:
      [f (⊔ c) = ⊔ (map_chain f c)]
    This is just unfolding [continuous]. 
*)
Lemma cont_apply_sup {D E : CPO.type} (f : [D →c E]) (c : chain D) :
    f (⊔ c) = ⊔ (map_chain (cf_mono f) c).
Proof.
    exact (cf_cont f c).
Qed.

(*
    Image of sup under a cont_fun, stated in the other direction for
    convenience in proofs that need the ⊑ form. 
*)
Lemma cont_apply_sup_le {D E : CPO.type} (f : [D →c E]) (c : chain D) (n : nat) :
    f (c.[n]) ⊑ f (⊔ c).
Proof.
    apply mf_mono.
    apply sup_upper.
Qed.

(*
    The sup of the image of [map_chain f c] is ⊑ the sup of [map_chain g c]
    whenever [f x ⊑ g x] for all x. 
*)
Lemma sup_map_chain_le {D E : CPO.type} (f g : mono_fun D E) (c : chain D) :
    (forall x, f x ⊑ g x) ->
    ⊔ (map_chain f c) ⊑ ⊔ (map_chain g c).
Proof.
    intros Hle.
    apply sup_mono; intros n.
    exact (Hle (c.[n])).
Qed.

End SupMapChain.


(* ================================================================== *)
(*   Scott continuity                                                 *)
(* ================================================================== *)

Section ContinuityLemmas.

(*
    A monotone function is continuous if and only if it satisfies the
    one-sided inequality [f (⊔ c) ⊑ ⊔ (map_chain f c)] for all chains.
    The other direction ([⊔ (map_chain f c) ⊑ f (⊔ c)]) is free from
    monotonicity alone (proved as [mono_sup_le] above).

    This gives a simpler sufficient condition for proving continuity:
    rather than establishing equality, it suffices to show [f (⊔ c) ⊑ ⊔ ...].
*)
Lemma continuous_of_le {D E : CPO.type} (f : mono_fun D E) :
    (forall c : chain D, f (⊔ c) ⊑ ⊔ (map_chain f c)) ->
    continuous f.
Proof.
    intros Hle c.
    apply le_antisym.
    - exact (Hle c).
    - exact (mono_sup_le f c).
Qed.

(*
    Continuity implies: the image of a sup is the sup of the image.
    (This is literally the definition, but stated in both directions
    as named lemmas for proof readability.) 
*)
Lemma continuous_sup_le {D E : CPO.type} (f : mono_fun D E)
    (Hcont : continuous f) (c : chain D) :
    f (⊔ c) ⊑ ⊔ (map_chain f c).
Proof.
    rewrite Hcont; apply le_refl.
Qed.

Lemma continuous_le_sup {D E : CPO.type} (f : mono_fun D E)
    (c : chain D) :
    ⊔ (map_chain f c) ⊑ f (⊔ c).
Proof.
    exact (mono_sup_le f c).
Qed.

(*
    Continuity of [f] is equivalent to the pair of inequalities: 
*)
Lemma continuous_iff_le {D E : CPO.type} (f : mono_fun D E) :
    continuous f <->
    forall c : chain D,
      f (⊔ c) ⊑ ⊔ (map_chain f c) /\ ⊔ (map_chain f c) ⊑ f (⊔ c).
Proof.
    split.
    - intros Hcont; split.
        + exact (continuous_sup_le f Hcont c).
        + exact (continuous_le_sup f c).
    - intros H.
      apply continuous_of_le.
      apply H.
Qed.

(*
    Extensionality for [cont_fun]: two continuous functions that agree
    on all inputs are equal.
    Proof uses [functional_extensionality] to equate the underlying
    functions, then [proof_irrelevance] for the monotonicity and
    continuity proofs. 
*)
Lemma cont_fun_ext {D E : CPO.type} (f g : [D →c E]) :
    (forall x, f x = g x) -> f = g.
Proof.
    intros Hext.
    apply (cont_fun_eq f g).
    destruct (cf_mono f) as [ff Hfm], (cf_mono g) as [gf Hgm].
    simpl in *.
    assert (Hf : ff = gf) by (apply functional_extensionality; exact Hext).
    subst gf.
    f_equal.
    apply proof_irrelevance.
Qed.

(*
    Extensionality for [mono_fun] (analogous to above). 
*)
Lemma mono_fun_ext {P Q : Preorder.type} (f g : mono_fun P Q) :
    (forall x, f x = g x) -> f = g.
Proof.
    intros Hext.
    destruct f as [ff Hfm], g as [gf Hgm].
    simpl in *.
    assert (Hf : ff = gf) by (apply functional_extensionality; exact Hext).
    subst gf.
    f_equal.
    apply proof_irrelevance.
Qed.

(*
    A continuous function applied to a chain_shift gives the same sup:
      [f (⊔ c) = ⊔ (map_chain f (chain_shift k c))]
    because [⊔ (chain_shift k c) = ⊔ c] and continuity.
*)
Lemma cont_apply_sup_shift {D E : CPO.type} (f : [D →c E]) (k : nat) (c : chain D) :
    f (⊔ c) = ⊔ (map_chain (cf_mono f) (chain_shift k c)).
Proof.
    rewrite <- sup_shift with (k := k).
    exact (cf_cont f (chain_shift k c)).
Qed.

(*
    A continuous function commutes with the tail chain sup: 
*)
Lemma cont_apply_sup_tail {D E : CPO.type} (f : [D →c E]) (c : chain D) :
    f (⊔ c) = ⊔ (map_chain (cf_mono f) (tail_chain c)).
Proof.
    rewrite <- sup_tail.
    exact (cf_cont f (tail_chain c)).
Qed.

End ContinuityLemmas.


(* ================================================================== *)
(*   Admissible predicates and chain Scott induction                  *)
(* ================================================================== *)
(*
    A predicate [P : D → Prop] on a CPO is _admissible_ if it is
    closed under suprema of chains:
      if [P (c.[n])] holds for all [n], then [P (⊔ c)] holds.

    Admissibility is the key concept for the fixpoint induction principle
    (Scott induction), which states: if [P] is admissible, [P ⊥] holds,
    and [P (f^n ⊥)] holds for all [n], then [P (fix f)] holds.  The
    fixpoint-specific form lives in [FixedPoints.v]; here we establish
    the chain-level theory.

    Reference: A&J §2.2; Benton-Kennedy-Varming (2009) §2.1 [admissible], [fixp_ind].
*)

Definition admissible {D : CPO.type} (P : D -> Prop) : Prop :=
  forall (c : chain D), (forall n, P (c.[n])) -> P (⊔ c).

Section AdmissibilityLemmas.
Context {D : CPO.type}.

(*
    Unfolding admissibility as a named lemma (sometimes cleaner in proofs). 
*)
Lemma scott_induction_chain (P : D -> Prop) (c : chain D) :
    admissible P -> (forall n, P (c.[n])) -> P (⊔ c).
Proof.
    intros Hadm Hchain.
    exact (Hadm c Hchain).
Qed.

(*
    The trivially-true predicate is admissible. 
*)
Lemma admissible_true : @admissible D (fun _ => True).
Proof.
    intros c _; exact I.
Qed.

(*
    The conjunction of two admissible predicates is admissible. 
*)
Lemma admissible_and (P Q : D -> Prop) :
    admissible P -> admissible Q -> admissible (fun x => P x /\ Q x).
Proof.
    intros HP HQ c Hchain.
    split.
    - apply HP; intros n. exact (proj1 (Hchain n)).
    - apply HQ; intros n. exact (proj2 (Hchain n)).
Qed.

(*
    The universal quantification of an admissible family is admissible. 
*)
Lemma admissible_forall {I : Type} (P : I -> D -> Prop) :
    (forall i, admissible (P i)) ->
    admissible (fun x => forall i, P i x).
Proof.
    intros HP c Hchain i.
    apply HP; intros n.
    exact (Hchain n i).
Qed.

(*
    The ordering predicate [⊑ x] is admissible: [⊔ c ⊑ x] if all [c.[n] ⊑ x].
    (This is just [sup_least] restated as admissibility.) 
*)
Lemma admissible_le (x : D) : admissible (fun y => y ⊑ x).
Proof.
    intros c Hchain.
    exact (sup_least c x Hchain).
Qed.

(*
    [⊑ ⊔ d] is admissible for any fixed chain [d]: the set of elements
    below the sup of [d] is closed under sups.
    Proof: if [c.[n] ⊑ ⊔ d] for all [n], then [⊔ c ⊑ ⊔ d] by [sup_least].
*)
Lemma admissible_le_sup (d : chain D) : admissible (fun x => x ⊑ ⊔ d).
Proof.
    apply admissible_le.
Qed.

(*
    The equality predicate [= x] is admissible when [x] is itself
    the sup of a chain that matches the given chain.  This is a degenerate
    case; the more useful form is [admissible_eq_sup] below. 
*)
Lemma admissible_eq_const (x : D) :
    admissible (fun y => y = x) <->
    forall (c : chain D), (forall n, c.[n] = x) -> ⊔ c = x.
Proof.
    split.
    all: intros H c Hchain; exact (H c Hchain).
Qed.

(*
    Image of an admissible predicate under a continuous function is admissible:
    if [P] is admissible on [E] and [f : D →c E], then [fun x => P (f x)] is admissible. 
*)
Lemma admissible_preimage {E : CPO.type} (f : [D →c E]) (P : E -> Prop) :
    admissible P -> admissible (fun x => P (f x)).
Proof.
    intros HP c Hchain.
    rewrite (cf_cont f c).
    apply HP; intros n.
    exact (Hchain n).
Qed.

End AdmissibilityLemmas.


(* ================================================================== *)
(*   PointedCPO consequences                                          *)
(* ================================================================== *)
(*
    Additional lemmas that require the bottom element [⊥]. 
*)

Section PointedCPOLemmas.
Context {D : PointedCPO.type}.

(** [⊥] is below every supremum. *)
Lemma bottom_le_sup (c : chain D) : ⊥ ⊑ ⊔ c.
Proof.
    exact (bottom_least (⊔ c)).
Qed.

(** The sup of the constant-[⊥] chain is [⊥]. *)
Lemma sup_const_bot : ⊔ (const_chain (⊥ : D)) = ⊥.
Proof.
    exact (sup_const_chain ⊥).
Qed.

(*
    [⊥] is admissible (trivially, since it holds for the zero-th element
    of any chain starting at ⊥).  More precisely: [fun x => x = ⊥] is NOT
    admissible in general (the sup of a chain of ⊥'s is ⊥, but an ascending
    chain starting at ⊥ may have sup ≠ ⊥).  We therefore do not state this.

    What IS true: the predicate [fun x => ⊥ ⊑ x] is admissible (it's always
    true), and [⊥] is a lower bound for every element, which is all we need
    for the Kleene fixed-point construction.
*)

(** [⊥] is below every element (re-export of [bottom_least] for convenience). *)
Lemma bottom_least_alt (x : D) : ⊥ ⊑ x.
Proof.
    exact (bottom_least x).
Qed.

(*
    In a pointed CPO, every chain [c] with [c.[0] = ⊥] satisfies [⊥ ⊑ ⊔ c]
    (which is just [bottom_le_sup], but stated in terms of the first element).
*)
Lemma bottom_le_sup_of_chain_start (c : chain D) :
    c.[0] = ⊥ -> ⊥ ⊑ ⊔ c.
Proof.
    intros _; exact (bottom_least (⊔ c)).
Qed.

(*
    Monotone functions between pointed CPOs send ⊥ somewhere above ⊥ in the codomain. 
*)
Lemma mono_bottom_le {E : PointedCPO.type} (f : mono_fun D E) :
    (⊥ : E) ⊑ f ⊥.
Proof.
    exact (bottom_least (f ⊥)).
Qed.

End PointedCPOLemmas.