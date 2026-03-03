(*  FixedPoints

    Phase 0: The Kleene fixed-point theorem for pointed omega-CPOs.

    This is [src/theory/FixedPoints.v].

    Imports:
      [src/structures/Order.v]     — chain, mono_fun
      [src/structures/CPO.v]       — CPO, PointedCPO
      [src/structures/Morphisms.v] — cont_fun
      [src/theory/CPOTheory.v]     — sup_least, sup_upper, sup_tail,
                                     sup_mono, sup_ext, admissible

    Summary
    =======
    For a Scott-continuous endomorphism [f : D →c D] on a pointed ω-CPO,
    the _Kleene fixed point_ is the supremum of the iteration chain:

        ⊥  ⊑  f(⊥)  ⊑  f²(⊥)  ⊑  f³(⊥)  ⊑  ...

    This supremum [fixp f] is the _least_ fixed point of [f] (the least
    element satisfying [f x = x]), and the least prefixed point
    (the least [x] satisfying [f x ⊑ x]).

    The key results:
    - [fixp_is_fixedpoint] : [f (fixp f) = fixp f]
    - [fixp_least]         : [f x ⊑ x → fixp f ⊑ x]
    - [fixp_ind]           : Scott's fixed-point induction principle
    - [fixp_mono]          : [fixp] is monotone in [f] (pointwise order)

    Note on FIXP
    ============
    [FIXP : cont_fun (cont_fun_cpo D D) D] — the fixed-point operator as a
    continuous function from the function-space CPO to [D] — is stated at the
    end of this file but its proof is deferred to [FunctionSpaces.v], since
    stating it requires [cont_fun D D] to carry a [CPO.type] structure
    (the pointwise CPO), which is constructed there.

    References: Abramsky & Jung §2.1.3; Benton-Kennedy §2.1.

    Contents:
    - §1  Iteration operator [iter]
    - §2  Kleene chain and the fixed point [fixp]
    - §3  [fixp] is a fixed point
    - §4  [fixp] is the least fixed point
    - §5  Fixed-point induction (Scott induction)
    - §6  Monotonicity of [fixp] in [f]
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory ChainTheory CPOTheory.


(* ================================================================== *)
(*   §1  Iteration operator                                           *)
(* ================================================================== *)
(*
    [iter f n] is the [n]-th iterate of [f] applied to [⊥]:
      iter f 0     = ⊥
      iter f (S n) = f (iter f n)

    We use a [Fixpoint] so that both equations hold definitionally —
    this is essential for the chain equality proofs in §3 to go through
    by [reflexivity] without any unfolding.
*)

Section Iter.
Context {D : PointedCPO.type}.

Fixpoint iter (f : cont_fun D D) (n : nat) : D :=
  match n with
  | O   => ⊥
  | S k => f (iter f k)
  end.

(** Both equations are definitional. *)
Lemma iter_zero (f : cont_fun D D) : iter f 0 = ⊥.
Proof.
    reflexivity.
Qed.

Lemma iter_succ (f : cont_fun D D) (n : nat) : iter f (S n) = f (iter f n).
Proof. 
    reflexivity. 
Qed.

(*
    The iteration sequence is monotone: [iter f n ⊑ iter f (S n)] for all [n].
    Proof by induction:
    - n = 0: [⊥ ⊑ f(⊥)] by [bottom_least].
    - S n:   [f(iter f n) ⊑ f(iter f (S n))] by monotonicity and the IH.
*)
Lemma iter_succ_le (f : cont_fun D D) (n : nat) : iter f n ⊑ iter f (S n).
Proof.
    induction n.
    - exact (bottom_least (f ⊥)).
    - simpl in *.
      apply @cf_mono.
      exact IHn.
Qed.

(*
    The iteration sequence is weakly increasing: [m ≤ n → iter f m ⊑ iter f n].
    Proof by induction on the proof of [m ≤ n].
*)
Lemma iter_mono (f : cont_fun D D) {m n : nat} (H : m <= n) :
    iter f m ⊑ iter f n.
Proof.
    induction H.
    - apply @le_refl.
    - eapply @le_trans.
        + exact IHle.
        + exact (iter_succ_le f _).
Qed.

(*
    [iter f] is monotone in [f] pointwise: if [∀ x, f x ⊑ g x],
    then [iter f n ⊑ iter g n] for all [n].
    Proof by induction on [n]:
    - 0: [⊥ ⊑ ⊥] by [le_refl].
    - S n: [f(iter f n) ⊑ f(iter g n)] by mono of [f] and IH,
           then [⊑ g(iter g n)] by the pointwise bound.
*)
Lemma iter_mono_fun (f g : cont_fun D D)
    (Hle : forall x, f x ⊑ g x) (n : nat) :
    iter f n ⊑ iter g n.
Proof.
    induction n.
    - exact (le_refl ⊥).
    - simpl. 
      apply @le_trans with (f (iter g n)).
        + apply @cf_mono. exact IHn.
        + exact (Hle (iter g n)).
Qed.

End Iter.


(* ================================================================== *)
(*  §2  The Kleene chain and fixed point                              *)
(* ================================================================== *)
(*
    The _Kleene chain_ of [f] is the ω-chain [n ↦ iter f n]:
        ⊥  ⊑  f(⊥)  ⊑  f²(⊥)  ⊑  ...

    The Kleene fixed point is the supremum of this chain.
*)

Section KleeneChain.
Context {D : PointedCPO.type}.

Definition kleene_chain (f : cont_fun D D) : chain D :=
  Build_chain (iter f) (fun m n H => iter_mono f H).

Lemma kleene_chain_index (f : cont_fun D D) (n : nat) :
    (kleene_chain f).[n] = iter f n.
Proof.
    reflexivity.
Qed.

(** The Kleene fixed point. *)
Definition fixp (f : cont_fun D D) : D := ⊔ (kleene_chain f).

End KleeneChain.


(* ================================================================== *)
(*   §3  [fixp f] is a fixed point of [f]                             *)
(* ================================================================== *)
(*
    [f (fixp f) = fixp f].

    Proof:
      f (fixp f) = f (⊔ kc)               [unfold fixp]
               = ⊔ (map_chain f kc)        [continuity of f]
               = ⊔ (tail_chain kc)         [sup_ext: the chains agree pointwise]
               = ⊔ kc                      [sup_tail]
               = fixp f                    [unfold fixp]

    The key step — that [map_chain f kc] and [tail_chain kc] agree
    pointwise — holds by [reflexivity]: both are definitionally
    [iter f (S n)] at index [n].
*)

Section FixpIsFixedPoint.
Context {D : PointedCPO.type}.

(*
    [map_chain f (kleene_chain f)] and [tail_chain (kleene_chain f)] agree
    pointwise (both equal [iter f (S n)] at each index). 
*)
Lemma kleene_map_eq_tail (f : cont_fun D D) (n : nat) :
    (map_chain (cf_mono f) (kleene_chain f)).[n] =
    (tail_chain (kleene_chain f)).[n].
Proof.
    reflexivity.
Qed.

Theorem fixp_is_fixedpoint (f : cont_fun D D) : f (fixp f) = fixp f.
Proof.
  unfold fixp.
  rewrite cf_cont.
  eapply eq_trans.
  - apply (@sup_ext D
      (map_chain (cf_mono f) (kleene_chain f))
      (tail_chain (kleene_chain f))).
    intro n.
    exact (kleene_map_eq_tail f n).
  - apply @sup_tail.
Qed.

(*
    Equivalent formulation: unfolding one application of [f].
    This is just [fixp_is_fixedpoint] restated, sometimes useful for
    rewriting in the other direction.
*)
Lemma fixp_unfold (f : cont_fun D D) : fixp f = f (fixp f).
Proof.
    exact (eq_sym (fixp_is_fixedpoint f)).
Qed.

(*
    [fixp f] is a prefixed point: [f (fixp f) ⊑ fixp f].
    Immediate from the fixed-point equation. 
*)
Lemma fixp_is_prefixedpoint (f : cont_fun D D) : f (fixp f) ⊑ fixp f.
Proof.
    rewrite fixp_is_fixedpoint; apply le_refl.
Qed.

(*
    [fixp f] is a postfixed point: [fixp f ⊑ f (fixp f)].
    Also immediate. 
*)
Lemma fixp_is_postfixedpoint (f : cont_fun D D) : fixp f ⊑ f (fixp f).
Proof.
    rewrite fixp_is_fixedpoint; apply @le_refl.
Qed.

(*
    Each iterate is below the fixed point.
*)
Lemma iter_le_fixp (f : cont_fun D D) (n : nat) : iter f n ⊑ fixp f.
Proof.
    unfold fixp.
    exact (sup_upper (kleene_chain f) n).
Qed.

End FixpIsFixedPoint.


(* ================================================================== *)
(*   §4  [fixp f] is the LEAST fixed point                            *)
(* ================================================================== *)
(*
    [fixp f] is not just any fixed point — it is the least one.
    More precisely, it is the least _prefixed_ point: if [f x ⊑ x], then
    [fixp f ⊑ x].  Since every fixed point [f x = x] is in particular a
    prefixed point, [fixp f] is below every fixed point.

    Proof of [fixp_least]: by induction show [iter f n ⊑ x] for all [n]:
    - n = 0: [⊥ ⊑ x] by [bottom_least].
    - S n:   [iter f (S n) = f (iter f n) ⊑ f x ⊑ x]
             using the IH and monotonicity of [f], then [f x ⊑ x].
    Then [fixp f = ⊔ kc ⊑ x] by [sup_least].
*)

Section FixpLeast.
Context {D : PointedCPO.type}.

(*
    Every iterate is below any prefixed point. 
*)
Lemma iter_le_prefixedpoint (f : cont_fun D D) (x : D)
    (Hfx : f x ⊑ x) (n : nat) : iter f n ⊑ x.
Proof.
  induction n.
  - exact (bottom_least x).
  - exact (le_trans _ _ _ (mf_mono (cf_mono f) _ _ IHn) Hfx).
Qed.

(*
    [fixp f] is the least prefixed point of [f]. 
*)
Theorem fixp_least (f : cont_fun D D) (x : D) :
    f x ⊑ x -> fixp f ⊑ x.
Proof.
    intros Hfx.
    unfold fixp.
    apply @sup_least; intros n.
    exact (iter_le_prefixedpoint f x Hfx n).
Qed.

(*
    Consequently, [fixp f] is the least fixed point of [f]. 
*)
Corollary fixp_least_fixedpoint (f : cont_fun D D) (x : D) :
    f x = x -> fixp f ⊑ x.
Proof.
    intros Heq.
    apply fixp_least.
    rewrite Heq; apply le_refl.
Qed.

(*
    Characterisation: [fixp f] is uniquely determined by being a
    fixed point that is below every prefixed point.
*)
Lemma fixp_characterisation (f : cont_fun D D) (x : D) :
    f x = x ->
    (forall y, f y ⊑ y -> x ⊑ y) ->
    x = fixp f.
Proof.
    intros Hfix Hleast.
    apply le_antisym.
    - apply Hleast.
      rewrite fixp_is_fixedpoint.
      apply le_refl.
    - exact (fixp_least_fixedpoint f x Hfix).
Qed.

(*
    [⊥] is below [fixp f]: the Kleene sequence starts below the fixed point. 
*)
Lemma bottom_le_fixp (f : cont_fun D D) : (⊥ : D) ⊑ fixp f.
Proof.
    exact (bottom_least (fixp f)).
Qed.

End FixpLeast.


(* ================================================================== *)
(*   §5  Fixed-point induction (Scott's induction principle)          *)
(* ================================================================== *)
(*
    The _fixed-point induction principle_ states: to prove a property [P]
    of [fixp f], it suffices to show:
    1. [P] is admissible (closed under ω-chain sups);
    2. [P ⊥];
    3. [P x → P (f x)] for all [x].

    Proof: (1) and (3) combine to give [P (iter f n)] for all [n] by
    induction.  Then (1) gives [P (⊔ (kleene_chain f))] = [P (fixp f)].

    This is the primary tool for proving properties of recursively-defined
    programs in the denotational semantics (Phase 1).

    Reference: A&J §2.1.3 Proposition 2.1.17; Benton-Kennedy [fixp_ind].
*)

Section FixpInd.
Context {D : PointedCPO.type}.

(*
    Every iterate satisfies [P], given the three hypotheses. 
*)
Lemma iter_satisfies (f : cont_fun D D) (P : D -> Prop) :
    P ⊥ ->
    (forall x, P x -> P (f x)) ->
    forall n, P (iter f n).
Proof.
    intros Hbottom Hstep n.
    induction n.
    - exact Hbottom.
    - exact (Hstep _ IHn).
Qed.

(*
    Scott fixed-point induction. 
*)
Theorem fixp_ind (f : cont_fun D D) (P : D -> Prop) :
    admissible P ->
    P ⊥ ->
    (forall x, P x -> P (f x)) ->
    P (fixp f).
Proof.
    intros Hadm Hbottom Hstep.
    unfold fixp.
    apply Hadm; intros n.
    rewrite (@kleene_chain_index D).
    exact (iter_satisfies f P Hbottom Hstep n).
Qed.

(*
    Variant: induction up to a bound.  If [P] holds at ⊥ and is preserved
    by [f], then [P (iter f n)] for every [n]. 
*)
Lemma fixp_ind_iterate (f : cont_fun D D) (P : D -> Prop) (n : nat) :
    P ⊥ ->
    (forall x, P x -> P (f x)) ->
    P (iter f n).
Proof.
    intros Hbottom Hstep.
    exact (iter_satisfies f P Hbottom Hstep n).
Qed.

(*
    A refinement using the preimage-admissibility from CPOTheory:
    if [P = Q ∘ g] for some [g : cont_fun D E] and admissible [Q] on [E],
    then [P] is admissible and we can apply [fixp_ind] directly. 
*)
Lemma fixp_ind_preimage {E : CPO.type}
    (f : cont_fun D D) (g : cont_fun D E) (Q : E -> Prop) :
    admissible Q ->
    Q (g ⊥) ->
    (forall x, Q (g x) -> Q (g (f x))) ->
    Q (g (fixp f)).
Proof.
    intros Hadm Hbottom Hstep.
    apply fixp_ind.
    - exact (admissible_preimage g Q Hadm).
    - exact Hbottom.
    - exact Hstep.
Qed.

(*
    The inequality form of fixed-point induction:
    to show [fixp f ⊑ x], it suffices to show [f x ⊑ x].
    (This is [fixp_least], restated in induction-principle style.) 
*)
Lemma fixp_ind_le (f : cont_fun D D) (x : D) :
    f x ⊑ x -> fixp f ⊑ x.
Proof.
    exact (fixp_least f x).
Qed.

End FixpInd.


(* ================================================================== *)
(*   §6  Monotonicity of [fixp] in [f]                                *)
(* ================================================================== *)
(*
    [fixp] is monotone with respect to the pointwise order on continuous
    functions: if [f x ⊑ g x] for all [x], then [fixp f ⊑ fixp g].

    Proof: show [iter f n ⊑ iter g n] for all [n] by induction
    (this is [iter_mono_fun] from §1), then apply [sup_mono]. 
*)

Section FixpMono.
Context {D : PointedCPO.type}.

Theorem fixp_mono (f g : cont_fun D D) :
    (forall x, f x ⊑ g x) -> fixp f ⊑ fixp g.
Proof.
    intros Hle.
    unfold fixp.
    apply @sup_mono.
    apply (@iter_mono_fun D).
    exact Hle.
Qed.

(*
    Pointwise equality of [f] and [g] implies equality of their fixed points.
    Proof: two applications of [fixp_mono]. 
*)
Corollary fixp_mono_eq (f g : cont_fun D D) :
    (forall x, f x = g x) -> fixp f = fixp g.
Proof.
    intros Heq.
    apply le_antisym; apply fixp_mono.
    all: intros x; rewrite Heq; apply le_refl.
Qed.

(*
    [fixp] is strictly above [⊥] when [f] is not the identity on [⊥]
    (i.e. when [f ⊥ ≠ ⊥]).  We state the contrapositive: if [fixp f = ⊥],
    then every iterate is [⊥].
*)
Lemma fixp_eq_bottom_iter (f : cont_fun D D) :
    fixp f = ⊥ -> forall n, iter f n = ⊥.
Proof.
    intros Hbottom n.
    apply le_antisym.
    - rewrite <- Hbottom.
      exact (iter_le_fixp f n).
    - exact (bottom_least (iter f n)).
Qed.

(*
    Iteration of the identity gives [⊥] at every step,
    and [fixp (cont_id D) = ⊥]. 
*)
Lemma fixp_id : fixp (cont_id D) = ⊥.
Proof.
    apply le_antisym.
    - apply fixp_least. apply le_refl.
    - exact (bottom_least _).
Qed.

End FixpMono.


(* ================================================================== *)
(*  Note on FIXP                                                       *)
(* ================================================================== *)
(*
    The _internalized_ fixed-point operator

        FIXP : cont_fun (cont_fun_cpo D D) D

    where [cont_fun_cpo D D] is the function-space CPO (continuous
    functions from [D] to [D] ordered pointwise), is deferred to
    [src/theory/FunctionSpaces.v].  There the function-space CPO
    [D ⇒c D] is constructed as a [CPO.type], and we can state:

        FIXP := Build_cont_fun fixp_mono_fun fixp_continuous

    where:
    - [fixp_mono_fun : mono_fun (D ⇒c D) D] wraps [fixp] together
      with [fixp_mono] as its monotonicity witness;
    - [fixp_continuous : continuous fixp_mono_fun] is proved via the
      double-sup / diagonal argument using [coherent_family] from
      [ChainTheory.v].

    The double-sup argument:
      fixp (⊔_n f_n) = ⊔_k (⊔_n f_n)^k(⊥) = ⊔_k ⊔_n f_n^k(⊥)
                     = ⊔_n ⊔_k f_n^k(⊥) = ⊔_n (fixp f_n)
    where the two sups commute because the family [k ↦ n ↦ f_n^k(⊥)]
    is coherent in the sense of [ChainTheory.coherent_family].

    Reference: A&J §2.1.3 Proposition 2.1.18; Benton-Kennedy [FIXP].
*)