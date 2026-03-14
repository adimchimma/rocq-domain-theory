(*  Sums

    Phase 0: The separated sum of two CPOs.

    This is [src/theory/Sums.v].

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, PointedCPO
      [src/structures/Morphisms.v] — cont_fun
      [src/theory/OrderTheory.v]   — chain_zero_le, le_antisym
      [src/theory/CPOTheory.v]     — sup_upper, sup_least, sup_ext,
                                     continuous_of_le, mono_sup_le

    Summary
    =======
    For two CPOs [D] and [E], the carrier type [D + E] (Coq's built-in sum)
    becomes a CPO under the _separated_ sum order:

        inl a  ⊑  inl a'   iff   a ⊑ a'   (in D)
        inr b  ⊑  inr b'   iff   b ⊑ b'   (in E)
        inl _  ⊑  inr _    =     False
        inr _  ⊑  inl _    =     False

    The key property used to construct suprema is:

        Any ω-chain [c] in [D + E] is eventually entirely in [inl] or
        entirely in [inr].

    In fact the chain is _immediately_ constant in summand: since the sum
    order never allows crossing from [inl] to [inr] or vice versa, once
    [c.[0]] is in [inl], every element is in [inl] (by chain monotonicity
    and the vacuous False branch in the other case).

    The supremum of [c] is therefore computed by matching on [c.[0]]:
    - If [c.[0] = inl d]:  [⊔ c = inl (⊔ (map_chain (extract_left d) c))]
    - If [c.[0] = inr e]:  [⊔ c = inr (⊔ (map_chain (extract_right e) c))]

    This definition requires no classical logic.

    Note: The separated sum [D + E] is NOT a pointed CPO even when [D] and
    [E] are, because [inl ⊥] and [inr ⊥] are incomparable — there is no
    least element of [D + E].  For a pointed sum one would add a fresh
    bottom (the "smash sum" or "lifted sum" [(D + E)⊥]).

    Contents:
    - §1  Sum order — HB instance registrations
    - §2  Extraction functions — [extract_left], [extract_right], monotonicity
    - §3  Chain stability — a chain starting in [inl] stays in [inl]
    - §4  Componentwise sup — [sum_sup], [HasSup] and [IsCPO] instances
    - §5  Injections — [cont_inl], [cont_inr]
    - §6  Copairing and universal property — [sum_case], UP

    Phase coverage:
      Phase 0 — all sections
      Phase 1 — §6 used in PCF case-expression denotation
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory CPOTheory.


(* ================================================================== *)
(*   §1  Sum order                                                    *)
(* ================================================================== *)

Section SumOrder.
Context {D E : CPO.type}.

(*
    The separated sum order: elements in different summands are incomparable.
*)
Definition sum_le (x y : D + E) : Prop :=
  match x, y with
  | inl a, inl a' => a ⊑ a'
  | inr b, inr b' => b ⊑ b'
  | _,     _      => False
  end.

Lemma sum_le_refl (x : D + E) : sum_le x x.
Proof.
    destruct x; exact (le_refl _).
Qed.

Lemma sum_le_trans (x y z : D + E) :
    sum_le x y -> sum_le y z -> sum_le x z.
Proof.
    destruct x, y, z; simpl; eauto; try tauto.
    all: intros Hxy Hyz; exact (le_trans _ _ _ Hxy Hyz).
Qed.

Lemma sum_le_antisym (x y : D + E) :
    sum_le x y -> sum_le y x -> x = y.
Proof.
    destruct x, y; simpl; try exact (fun H _ => False_ind _ H).
    - intros Hxy Hyx; exact (f_equal inl (le_antisym _ _ Hxy Hyx)).
    - intros Hxy Hyx; exact (f_equal inr (le_antisym _ _ Hxy Hyx)).
Qed.

End SumOrder.

Open Scope type_scope.

HB.instance Definition sum_HasLe {D E : CPO.type} :=
    HasLe.Build (D + E) sum_le.

HB.instance Definition sum_IsPreorder {D E : CPO.type} :=
    IsPreorder.Build (D + E) sum_le_refl sum_le_trans.

HB.instance Definition sum_IsPartialOrder {D E : CPO.type} :=
    IsPartialOrder.Build (D + E) sum_le_antisym.

(*
    Convenient unfolding lemmas for the order on [D + E].
*)
Lemma sum_le_inl {D E : CPO.type} (a a' : D) :
    (inl a : D + E) ⊑ inl a' <-> a ⊑ a'.
Proof.
    reflexivity.
Qed.

Lemma sum_le_inr {D E : CPO.type} (b b' : E) :
    (inr b : D + E) ⊑ inr b' <-> b ⊑ b'.
Proof.
    reflexivity.
Qed.

Lemma sum_le_inl_inr_false {D E : CPO.type} (a : D) (b : E) :
    ~ (inl a : D + E) ⊑ inr b.
Proof.
    exact (fun H => H).
Qed.

Lemma sum_le_inr_inl_false {D E : CPO.type} (b : E) (a : D) :
    ~ (inr b : D + E) ⊑ inl a.
Proof.
    exact (fun H => H).
Qed.


(* ================================================================== *)
(*   §2  Extraction functions                                         *)
(* ================================================================== *)
(*
    [extract_left d x] returns the [inl]-component of [x], or [d] if [x = inr _].
    [extract_right e x] is symmetric.

    Both are monotone for any default value.  The key cases:
    - [inl/inl]: direct from the D-ordering.
    - [inr/inr]: both map to the default, which is ⊑ itself by [le_refl].
    - Mixed: [inl _ ⊑ inr _] and [inr _ ⊑ inl _] are [False], so the
      monotonicity proof goes through vacuously.
*)

Section Extraction.
Context {D E : CPO.type}.

Definition extract_left (d : D) (x : D + E) : D :=
  match x with inl a => a | inr _ => d end.

Definition extract_right (e : E) (x : D + E) : E :=
  match x with inl _ => e | inr b => b end.

Lemma extract_left_mono (d : D) :
    monotone (D + E) D (extract_left d).
Proof.
    intros x y Hxy.
    destruct x, y; simpl in *; try exact (False_ind _ Hxy).
    - exact Hxy.
    - exact (le_refl d).
Qed.

Lemma extract_right_mono (e : E) :
    monotone (D + E) E (extract_right e).
Proof.
    intros x y Hxy.
    destruct x, y; simpl in *; try exact (False_ind _ Hxy).
    - exact (le_refl e).
    - exact Hxy.
Qed.

Definition extract_left_mfun (d : D) : mono_fun (D + E) D :=
  Build_mono_fun (extract_left d) (extract_left_mono d).

Definition extract_right_mfun (e : E) : mono_fun (D + E) E :=
  Build_mono_fun (extract_right e) (extract_right_mono e).

(*
    On [inl]-values, [extract_left] is the identity.
    On [inr]-values, [extract_right] is the identity.
*)
Lemma extract_left_inl (d : D) (a : D) :
    extract_left d (inl a : D + E) = a.
Proof.
    reflexivity.
Qed.

Lemma extract_right_inr (e : E) (b : E) :
    extract_right e (inr b : D + E) = b.
Proof.
    reflexivity.
Qed.

End Extraction.


(* ================================================================== *)
(*   §3  Chain stability                                              *)
(* ================================================================== *)
(*
    A chain in [D + E] that starts in [inl] stays in [inl] forever.
    Proof: if [c.[0] = inl d] and [c.[n] = inr e], then
    [c.[0] ⊑ c.[n]] (by [chain_zero_le]) gives [inl d ⊑ inr e], which is
    [False] in the sum order.  Symmetric for chains starting in [inr].

    No classical logic is needed: we derive a contradiction directly from
    the chain monotonicity axiom and the sum order definition. 
*)

Section ChainStability.
Context {D E : CPO.type}.

Lemma chain_inl_stable (c : chain (D + E)) (d : D) (n : nat) :
    c.[0] = inl d -> exists a : D, c.[n] = inl a.
Proof.
    intros H0.
    destruct (c.[n]) eqn:Hn.
    - exists s. reflexivity.
    - exfalso.
      pose proof (chain_zero_le c n) as Hle.
      rewrite H0, Hn in Hle.
      exact Hle.
Qed.

Lemma chain_inr_stable (c : chain (D + E)) (e : E) (n : nat) :
    c.[0] = inr e -> exists b : E, c.[n] = inr b.
Proof.
    intros H0.
    destruct (c.[n]) eqn:Hn.
    - exfalso.
      pose proof (chain_zero_le c n) as Hle.
      rewrite H0, Hn in Hle.
      exact Hle.
    - exists s. reflexivity.
Qed.

(*
    Corollary: if [c.[n] = inl a] and [c.[n] ⊑ c.[m]], then [c.[m] = inl _].
    Useful for the continuity proof where we work from an arbitrary index.
*)
Lemma chain_inl_stable_from (c : chain (D + E)) (a : D) (n m : nat) :
    c.[n] = inl a -> n <= m -> exists a' : D, c.[m] = inl a'.
Proof.
    intros Hn Hnm.
    destruct (c.[m]) eqn:Hm.
    - exact (ex_intro _ s eq_refl).
    - exfalso.
      pose proof (ch_mono c n m Hnm) as Hle.
      rewrite Hn, Hm in Hle.
      exact Hle.
Qed.

End ChainStability.


(* ================================================================== *)
(*   §4  Componentwise sup                                            *)
(* ================================================================== *)
(*
    The sup of a chain [c : chain (D + E)] is computed by matching on [c.[0]]:
    - [c.[0] = inl d]: the whole chain lives in [inl] (by §3), so
      [⊔ c = inl (⊔ (map_chain (extract_left_mfun d) c))].
    - [c.[0] = inr e]: [⊔ c = inr (⊔ (map_chain (extract_right_mfun e) c))].
*)

Section SumSup.
Context {D E : CPO.type}.

Definition sum_sup (c : chain (D + E)) : D + E :=
  match c.[0] with
  | inl d => inl (⊔ (map_chain (extract_left_mfun d) c))
  | inr e => inr (⊔ (map_chain (extract_right_mfun e) c))
  end.

(* Unfolding lemmas for [sum_sup]. *)
Lemma sum_sup_inl (c : chain (D + E)) (d : D) :
    c.[0] = inl d ->
    sum_sup c = inl (⊔ (map_chain (extract_left_mfun d) c)).
Proof.
    intros H; unfold sum_sup; rewrite H; reflexivity.
Qed.

Lemma sum_sup_inr (c : chain (D + E)) (e : E) :
    c.[0] = inr e ->
    sum_sup c = inr (⊔ (map_chain (extract_right_mfun e) c)).
Proof.
    intros H; unfold sum_sup; rewrite H; reflexivity.
Qed.

(*
    [sum_sup c] is an upper bound of [c].

    Case [c.[0] = inl d]:
      For each [n], [c.[n] = inl a_n] (by [chain_inl_stable]).
      Then [(extract_left_mfun d (c.[n])) = a_n], so
      [c.[n] = inl a_n ⊑ inl (⊔ d_chain)] iff [a_n ⊑ ⊔ d_chain].
      The latter holds by [sup_upper].

    Case [c.[0] = inr e]: symmetric.
*)
Lemma sum_sup_upper (c : chain (D + E)) (n : nat) :
    c.[n] ⊑ sum_sup c.
Proof.
    unfold sum_sup.
    destruct (c.[0]) eqn:H0.
    - destruct (c.[n]) eqn:Hn.
      + simpl.
        replace s0 with ((map_chain (extract_left_mfun s) c).[n]).
        * exact (sup_upper _ n).
        * simpl. rewrite Hn. reflexivity.
      + exfalso.
        pose proof (chain_zero_le c n) as Hle.
        rewrite H0, Hn in Hle; exact Hle.
    - destruct (c.[n]) eqn:Hn.
      + exfalso.
        pose proof (chain_zero_le c n) as Hle.
        rewrite H0, Hn in Hle; exact Hle.
        + simpl.
          replace s0 with ((map_chain (extract_right_mfun s) c).[n]).
          * exact (sup_upper _ n).
          * apply (f_equal (extract_right s)) in Hn.
            simpl in Hn. simpl. exact Hn.
Qed.

(*
    [sum_sup c] is the least upper bound of [c].

    Case [c.[0] = inl d], [p = inl a]:
      Need [⊔ d_chain ⊑ a].  By [sup_least]: for each [n],
      [d_chain.[n] = extract_left d (c.[n])].
      - If [c.[n] = inl a_n]: [d_chain.[n] = a_n].
        [Hub n : inl a_n ⊑ inl a], i.e. [a_n ⊑ a]. ✓
      - If [c.[n] = inr b_n]: [Hub n : inr b_n ⊑ inl a = False]. Ex falso.

    Case [c.[0] = inl d], [p = inr b]:
      [Hub 0 : inl d ⊑ inr b = False]. Ex falso.
*)
Lemma sum_sup_least (c : chain (D + E)) (p : D + E) :
    (forall n, c.[n] ⊑ p) -> sum_sup c ⊑ p.
Proof.
    intros Hub.
    unfold sum_sup.
    destruct (c.[0]) eqn:H0.
    - destruct p as [a | b].
      + apply sup_least; intros n; simpl.
        destruct (c.[n]) eqn:Hn.
        * pose proof (Hub n) as Hbn.
          rewrite Hn in Hbn. simpl in Hbn. exact Hbn.
        * exfalso.
          pose proof (Hub n) as Hbn.
          rewrite Hn in Hbn. exact Hbn.
      + exfalso.
        pose proof (Hub 0) as Hb0.
        rewrite H0 in Hb0. exact Hb0.
    - destruct p as [a | b].
      + exfalso.
        pose proof (Hub 0) as Hb0.
        rewrite H0 in Hb0. exact Hb0.
      + apply sup_least; intros n; simpl.
        destruct (c.[n]) eqn:Hn.
        * exfalso.
          pose proof (Hub n) as Hbn.
          rewrite Hn in Hbn. exact Hbn.
        * pose proof (Hub n) as Hbn.
          rewrite Hn in Hbn. simpl in Hbn. exact Hbn.
Qed.

End SumSup.

HB.instance Definition sum_HasSup {D E : CPO.type} :=
  HasSup.Build (D + E) sum_sup.

HB.instance Definition sum_IsCPO {D E : CPO.type} :=
  IsCPO.Build (D + E) sum_sup_upper sum_sup_least.

(*
    The sup of a chain starting in [inl d] unfolds to [inl (⊔ projected_chain)].
    Stated after the instances so [⊔] notation works.
*)
Lemma sup_sum_inl {D E : CPO.type} (c : chain (D + E)) (d : D) :
    c.[0] = inl d ->
    ⊔ c = inl (⊔ (map_chain (extract_left_mfun d) c)).
Proof.
    exact (sum_sup_inl c d).
Qed.

Lemma sup_sum_inr {D E : CPO.type} (c : chain (D + E)) (e : E) :
    c.[0] = inr e ->
    ⊔ c = inr (⊔ (map_chain (extract_right_mfun e) c)).
Proof.
    exact (sum_sup_inr c e).
Qed.


(* ================================================================== *)
(*   §5  Injections                                                   *)
(* ================================================================== *)
(*
    [cont_inl : D →c D+E] and [cont_inr : E →c D+E] are the two
    canonical injections into the sum.

    Continuity: [inl (⊔ c) = ⊔ (map_chain inl_mono c)].
    The chain [map_chain inl_mono c] starts at [inl (c.[0])], so its sup
    is [inl (⊔ (extract_left_mfun (c.[0]) ∘ map_chain inl_mono ∘ c))]
    = [inl (⊔ c)] since [extract_left (c.[0]) (inl a) = a] for all a.
*)

Section SumInjections.
Context {D E : CPO.type}.

Definition inl_mono : mono_fun D (D + E) :=
  Build_mono_fun inl (fun a a' H => H).

Definition inr_mono : mono_fun E (D + E) :=
  Build_mono_fun inr (fun b b' H => H).

Lemma continuous_inl : continuous (inl_mono).
Proof.
    intros c; simpl.
    pose proof (sup_sum_inl (map_chain inl_mono c) (c.[0]) eq_refl) as Hsup.
    transitivity ((inl (⊔ (map_chain (extract_left_mfun (c.[0])) (map_chain inl_mono c))) : D + E)).
    - f_equal.
      apply sup_ext.
      intros n.
      reflexivity.
    - exact (eq_sym Hsup).
Qed.

Lemma continuous_inr : continuous (inr_mono).
Proof.
    intros c; simpl.
    pose proof (sup_sum_inr (map_chain inr_mono c) (c.[0]) eq_refl) as Hsup.
    transitivity ((inr (⊔ (map_chain (extract_right_mfun (c.[0])) (map_chain inr_mono c))) : D + E)).
    - f_equal.
      apply sup_ext.
      intros n.
      reflexivity.
    - exact (eq_sym Hsup).
Qed.

Definition cont_inl : [D →c (D + E)] :=
  Build_cont_fun inl_mono continuous_inl.

Definition cont_inr : [E →c (D + E)] :=
  Build_cont_fun inr_mono continuous_inr.

(* Thesis notation *)
Notation ι₁ := (cont_inl).
Notation ι₂ := (cont_inr).

End SumInjections.

Notation ι₁ := cont_inl.
Notation ι₂ := cont_inr.


(* ================================================================== *)
(* §6  Copairing and universal property                               *)
(* ================================================================== *)
(*
    Given [f : D →c F] and [g : E →c F], the _copairing_ [[f, g] : D+E →c F]
    is defined by case analysis:
        [f, g](inl a) = f a
        [f, g](inr b) = g b

    This satisfies the universal property of the sum:
        [f, g] ∘ ι₁ = f
        [f, g] ∘ ι₂ = g
    and is unique with this property.

    Continuity of [[f, g]]:
    Case [c.[0] = inl d]:
      [⊔ c = inl s] where [s = ⊔ (map_chain (extract_left d) c)].
      [[f,g](inl s) = f(s)].
      For all [n], [c.[n] = inl a_n], so [(map_chain [f,g] c).[n] = f(a_n)].
      And [(map_chain (extract_left d) c).[n] = a_n].
      So [⊔(map_chain [f,g] c) = ⊔(map_chain f (extract_left_chain))] by [sup_ext].
      Then [f(⊔(extract_left_chain)) = f(s)] by continuity of [f]. ✓
*)

Section SumCopairing.
Context {D E F : CPO.type}.

Definition sum_case_fun (f : [D →c F]) (g : [E →c F])
    (x : D + E) : F :=
  match x with inl a => f a | inr b => g b end.

Lemma sum_case_mono (f : [D →c F]) (g : [E →c F]) :
    monotone (D + E) F (sum_case_fun f g).
Proof.
    intros x y Hxy.
    destruct x, y; simpl in *; try exact (False_ind _ Hxy).
  - exact (mf_mono (cf_mono f) _ _ Hxy).
  - exact (mf_mono (cf_mono g) _ _ Hxy).
Qed.

Definition sum_case_mfun (f : [D →c F]) (g : [E →c F])
    : mono_fun (D + E) F :=
  Build_mono_fun (sum_case_fun f g) (sum_case_mono f g).

(*
    Continuity of [[f, g]].
    We case-split on [c.[0]] to determine the summand, then use chain
    stability to show all elements live in that summand, and finally
    reduce to continuity of [f] (or [g]).
*)
Lemma continuous_sum_case (f : [D →c F]) (g : [E →c F]) :
    continuous (sum_case_mfun f g).
Proof.
    intros c.
    destruct (c.[0]) eqn:H0.
    - pose proof (sup_sum_inl c s H0) as Hsup.
      transitivity (sum_case_fun f g (inl (⊔ (map_chain (extract_left_mfun s) c)))).
      + exact (f_equal (sum_case_fun f g) Hsup).
      + simpl.
        transitivity (⊔ (map_chain (cf_mono f) (map_chain (extract_left_mfun s) c))).
        * exact (cf_cont f (map_chain (extract_left_mfun s) c)).
        * apply sup_ext.
          intros n.
          destruct (chain_inl_stable c s n H0) as [a Ha].
          pose proof (f_equal (extract_left s) Ha) as Hleft.
          pose proof (f_equal (sum_case_fun f g) Ha) as Hcase.
          simpl in Hleft, Hcase.
          transitivity (f a).
          -- exact (f_equal f Hleft).
          -- exact (eq_sym Hcase).
    - pose proof (sup_sum_inr c s H0) as Hsup.
      transitivity (sum_case_fun f g (inr (⊔ (map_chain (extract_right_mfun s) c)))).
      + exact (f_equal (sum_case_fun f g) Hsup).
      + simpl.
        transitivity (⊔ (map_chain (cf_mono g) (map_chain (extract_right_mfun s) c))).
        * exact (cf_cont g (map_chain (extract_right_mfun s) c)).
        * apply sup_ext.
          intros n.
          destruct (chain_inr_stable c s n H0) as [b Hb].
          pose proof (f_equal (extract_right s) Hb) as Hright.
          pose proof (f_equal (sum_case_fun f g) Hb) as Hcase.
          simpl in Hright, Hcase.
          transitivity (g b).
          -- exact (f_equal g Hright).
          -- exact (eq_sym Hcase).
Qed.

Definition sum_case (f : [D →c F]) (g : [E →c F])
    : [(D + E) →c F] :=
  Build_cont_fun (sum_case_mfun f g) (continuous_sum_case f g).

(* β-reductions for [sum_case]. *)
Lemma sum_case_inl (f : [D →c F]) (g : [E →c F]) (a : D) :
    sum_case f g (inl a) = f a.
Proof.
    reflexivity.
Qed.

Lemma sum_case_inr (f : [D →c F]) (g : [E →c F]) (b : E) :
    sum_case f g (inr b) = g b.
Proof.
    reflexivity.
Qed.

(*
    Universal property: β-reductions stated as composition equalities. 
*)
Lemma sum_case_comp_inl (f : [D →c F]) (g : [E →c F]) :
    cont_comp (sum_case f g) cont_inl = f.
Proof.
    apply cont_fun_ext; intros a; reflexivity.
Qed.

Lemma sum_case_comp_inr (f : [D →c F]) (g : [E →c F]) :
    cont_comp (sum_case f g) cont_inr = g.
Proof.
    apply cont_fun_ext; intros b; reflexivity.
Qed.

(*
    η-expansion: any [h : D+E →c F] equals [sum_case (h ∘ ι₁) (h ∘ ι₂)]. 
*)
Lemma sum_case_eta (h : [(D + E) →c F]) :
    h = sum_case (cont_comp h cont_inl) (cont_comp h cont_inr).
Proof.
    apply cont_fun_ext; intros x.
    destruct x; reflexivity.
Qed.

(*
    Uniqueness: if [h ∘ ι₁ = f] and [h ∘ ι₂ = g], then [h = sum_case f g]. 
*)
Lemma sum_case_unique (f : [D →c F]) (g : [E →c F])
    (h : [(D + E) →c F]) :
    cont_comp h cont_inl = f ->
    cont_comp h cont_inr = g ->
    h = sum_case f g.
Proof.
    intros H1 H2.
    rewrite (sum_case_eta h), H1, H2.
    reflexivity.
Qed.

End SumCopairing.
Close Scope type_scope.

(*
    Functoriality: [sum_case (f ∘ ι₁ ∘ k) (f ∘ ι₂ ∘ k) = f ∘ k] for [k : D+E →c D'+E']. 
*)
Lemma sum_case_comp_fusion_poly
    {D E F F' : CPO.type}
    (f : [D →c F]) (g : [E →c F]) (h : [F →c F']) :
    cont_comp h (sum_case f g) =
    @sum_case D E F' (cont_comp h f) (cont_comp h g).
Proof.
    apply cont_fun_ext; intros x.
    destruct x; reflexivity.
Qed.