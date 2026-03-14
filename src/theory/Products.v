(*  Products

    Phase 0: The product of two CPOs.

    This is [src/theory/Products.v].

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, PointedCPO, HasSup, IsCPO
      [src/structures/Morphisms.v] — cont_fun, cont_comp, cont_id
      [src/theory/OrderTheory.v]   — le_antisym, pequiv_eq
      [src/theory/CPOTheory.v]     — sup_least, sup_upper, sup_ext, sup_mono,
                                     continuous_of_le, mono_sup_le

    Summary
    =======
    For two CPOs [D] and [E], the carrier type [D * E] (Coq's built-in
    product) becomes a CPO under the pointwise order:

        (a, b) ⊑ (c, d)  ↔  a ⊑ c  ∧  b ⊑ d

    The supremum of a chain [c : chain (D * E)] is computed componentwise:

        ⊔ c = (⊔ (map_chain π₁ c),  ⊔ (map_chain π₂ c))

    This choice makes the projections [π₁] and [π₂] automatically
    Scott-continuous: [π₁ (⊔ c)] unfolds to the first component of the
    sup, which is [⊔ (map_chain π₁ c)] by definition.

    The product satisfies the universal property of categorical products:
    for any [f : C →c D] and [g : C →c E], the pairing [⟨f, g⟩ : C →c D×E]
    is the unique continuous map with [π₁ ∘ ⟨f,g⟩ = f] and [π₂ ∘ ⟨f,g⟩ = g].

    Contents:
    - §1  Pointwise order on [D * E] — HB instance registrations
    - §2  Componentwise sup — [HasSup] and [IsCPO] instances
    - §3  Monotone projections and pairing
    - §4  Continuity of projections, pairing, and product map
    - §5  Universal property
    - §6  PointedCPO product

    Phase coverage:
      Phase 0 — all sections
      Phase 1 — §4 used in [EnrichedTheory.v] via separate continuity (DD-002)

    References:
      Benton, Kennedy & Varming (2009) §2 — product CPOs (implicit).
      Abramsky & Jung (1994) §2.2.4 — products of dcpos.
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory CPOTheory.

(* ================================================================== *)
(*   Pointwise order on [D * E]                                       *)
(* ================================================================== *)
(*
    The pointwise order on [D * E]:
        (a, b) ⊑ (c, d)  ↔  a ⊑ c  ∧  b ⊑ d
*)

Section ProdOrder.
Context {D E : CPO.type}.

Definition prod_le (p q : D * E) : Prop :=
  fst p ⊑ fst q /\ snd p ⊑ snd q.

Lemma prod_le_refl (p : D * E) : prod_le p p.
Proof.
    exact (conj (le_refl _) (le_refl _)).
Qed.

Lemma prod_le_trans (p q r : D * E) :
    prod_le p q -> prod_le q r -> prod_le p r.
Proof.
    intros [Hpq1 Hpq2] [Hqr1 Hqr2].
    exact (conj (le_trans _ _ _ Hpq1 Hqr1) (le_trans _ _ _ Hpq2 Hqr2)).
Qed.

Lemma prod_le_antisym (p q : D * E) :
    prod_le p q -> prod_le q p -> p = q.
Proof.
    intros [Hpq1 Hpq2] [Hqp1 Hqp2].
    destruct p as [a b], q as [c d]; simpl in *.
    exact (f_equal2 pair (le_antisym _ _ Hpq1 Hqp1) (le_antisym _ _ Hpq2 Hqp2)).
Qed.

End ProdOrder.


Open Scope type_scope.

(*
    Register the order structure on [D * E] for all [D E : CPO.type].
    After these instances, [⊑] on [D * E] denotes the pointwise order.
*)
HB.instance Definition prod_HasLe {D E : CPO.type} :=
    HasLe.Build (D * E) (prod_le).

HB.instance Definition prod_IsPreorder {D E : CPO.type} :=
    IsPreorder.Build (D * E) prod_le_refl prod_le_trans.

HB.instance Definition prod_IsPartialOrder {D E : CPO.type} :=
    IsPartialOrder.Build (D * E) prod_le_antisym.


(* ================================================================== *)
(*   Componentwise sup                                                *)
(* ================================================================== *)
(*
    The sup of a chain [c : chain (D * E)] is the pair of the sups of
    its component projections.  We first build the monotone projections
    on the now-ordered [D * E], then define the sup.
*)

Section ProdSup.
Context {D E : CPO.type}.

(*
    Monotone projections [fst_mono] and [snd_mono].
    These are used to form the component chains; the continuous versions
    come in §4. 
*)
Definition fst_mono : mono_fun (D * E) D :=
    Build_mono_fun fst (fun p q H => proj1 H).

Definition snd_mono : mono_fun (D * E) E :=
    Build_mono_fun snd (fun p q H => proj2 H).

(*
    The componentwise sup: [⊔ c = (⊔ (fst ∘ c), ⊔ (snd ∘ c))].
*)
Definition prod_sup (c : chain (D * E)) : D * E :=
    (⊔ (map_chain fst_mono c), ⊔ (map_chain snd_mono c)).

(*
    [prod_sup c] is an upper bound of [c]:
    [(c.[n]).1 ⊑ ⊔(map_chain fst_mono c)] and
    [(c.[n]).2 ⊑ ⊔(map_chain snd_mono c)] by [sup_upper]. 
*)
Lemma prod_sup_upper (c : chain (D * E)) (n : nat) :
    c.[n] ⊑ prod_sup c.
Proof.
    unfold prod_sup; split.
    - exact (sup_upper (map_chain fst_mono c) n).
    - exact (sup_upper (map_chain snd_mono c) n).
Qed.

(*
    [prod_sup c] is the least upper bound of [c]:
    if [(a, b)] is an upper bound, then [⊔ fst ≤ a] and [⊔ snd ≤ b]
    by [sup_least]. 
*)
Lemma prod_sup_least (c : chain (D * E)) (p : D * E) :
    (forall n, c.[n] ⊑ p) -> prod_sup c ⊑ p.
Proof.
    intros Hub.
    unfold prod_sup; split.
    - apply sup_least; intros n. exact (proj1 (Hub n)).
    - apply sup_least; intros n. exact (proj2 (Hub n)).
Qed.

End ProdSup.

(* Register the sup structure on [D * E]. *)
HB.instance Definition prod_HasSup {D E : CPO.type} :=
    HasSup.Build (D * E) prod_sup.

HB.instance Definition prod_IsCPO {D E : CPO.type} :=
    IsCPO.Build (D * E) prod_sup_upper prod_sup_least.


(* ================================================================== *)
(*   Monotone projections and pairing                                 *)
(* ================================================================== *)

Section ProdMono.
Context {D E : CPO.type}.

(*
    The sup of a chain in [D * E] unfolds component-by-component.
    These computation lemmas let us rewrite [⊔ c] in proofs. 
*)
Lemma prod_sup_fst (c : chain (D * E)) :
    fst (⊔ c) = ⊔ (map_chain fst_mono c).
Proof.
    reflexivity.
Qed.

Lemma prod_sup_snd (c : chain (D * E)) :
    snd (⊔ c) = ⊔ (map_chain snd_mono c).
Proof.
    reflexivity.
Qed.

(*
    Pairing of two monotone functions.
    [mono_pair f g (x) = (f x, g x)]. 
*)
Definition mono_pair {C D0 E0 : CPO.type}
    (f : mono_fun C D0) (g : mono_fun C E0)
    : mono_fun C (D0 * E0) :=
  Build_mono_fun
    (fun x => (f x, g x))
    (fun x y Hxy => conj (mf_mono f x y Hxy) (mf_mono g x y Hxy)).

Lemma mono_pair_fst {C : CPO.type} (f : mono_fun C D) (g : mono_fun C E)
    (x : C) : fst (mono_pair f g x) = f x.
Proof.
    reflexivity.
Qed.

Lemma mono_pair_snd {C : CPO.type} (f : mono_fun C D) (g : mono_fun C E)
    (x : C) : snd (mono_pair f g x) = g x.
Proof.
    reflexivity.
Qed.

(*
    Monotone product map: applies [f] to the first component and [g]
    to the second. 
*)
Definition mono_prod_map {D' E' : CPO.type}
    (f : mono_fun D D') (g : mono_fun E E')
    : mono_fun (D * E) (D' * E') :=
  mono_pair (mono_comp f fst_mono) (mono_comp g snd_mono).

End ProdMono.

(* ================================================================== *)
(*   Continuity of projections, pairing, and product map              *)
(* ================================================================== *)

Section ProdCont.
Context {D E : CPO.type}.

(*
    [π₁ : D×E →c D] is continuous.
    [π₁ (⊔ c) = fst (⊔ c) = ⊔(map_chain fst_mono c) = ⊔(map_chain π₁ c)]
    by [prod_sup_fst], which holds definitionally.
    We use [sup_ext] to equate the two image chains. 
*)
Lemma continuous_fst : continuous (fst_mono (D:=D)(E:=E)).
Proof.
    intros c. reflexivity.
Qed.

Definition π₁ : [(D * E) →c D] :=
  Build_cont_fun fst_mono continuous_fst.

(*
    [π₂ : D×E →c E] is continuous, by the same argument. 
*)
Lemma continuous_snd : continuous (snd_mono (D:=D)(E:=E)).
Proof.
    intros c. reflexivity.
Qed.

Definition π₂ : [(D * E) →c E] :=
  Build_cont_fun snd_mono continuous_snd.

(*
    Pairing of two continuous functions is continuous.

    Proof:
      ⟨f,g⟩(⊔ c) = (f(⊔c), g(⊔c))
                 = (⊔(map_chain f c), ⊔(map_chain g c))    [continuity of f, g]
                 = ⊔(map_chain ⟨f,g⟩ c)                    [prod_sup definition]

    The last equality holds because:
    - fst component of ⊔(map_chain ⟨f,g⟩ c) = ⊔(map_chain fst_mono (map_chain ⟨f,g⟩ c))
                                            = ⊔(map_chain f c)   [by sup_ext, reflexivity]
    - snd component similarly.
*)
Lemma continuous_pair {C D0 E0 : CPO.type}
    (f : [C →c D0]) (g : [C →c E0]) :
    continuous (mono_pair (cf_mono f) (cf_mono g)).
Proof.
    intros c.
    apply le_antisym.
    - split; simpl.
        + rewrite (cf_cont f c).
          apply sup_mono; intros n. apply le_refl.
        + rewrite (cf_cont g c).
          apply sup_mono; intros n. apply le_refl.
    - apply prod_sup_least; intros n; split; simpl.
        all: apply cf_mono; exact (sup_upper c n).
Qed.

(*
    The pairing as a [cont_fun].
    Notation: [⟨f, g⟩] in the thesis; [cont_pair f g] in Rocq. 
*)
Definition cont_pair {C D0 E0 : CPO.type}
    (f : [C →c D0]) (g : [C →c E0])
    : [C →c (D0 * E0)] :=
  Build_cont_fun (mono_pair (cf_mono f) (cf_mono g)) (continuous_pair f g).

Notation "⟨ f , g ⟩" := (cont_pair f g) (at level 0, f at level 99).

(*
    Continuity of the product map [f × g : D×E →c D'×E'].
    Follows from [continuous_pair] applied to [f ∘ π₁] and [g ∘ π₂]. 
*)
Lemma continuous_prod_map {D' E' : CPO.type}
    (f : [D →c D']) (g : [E →c E']) :
    continuous (mono_prod_map (cf_mono f) (cf_mono g)).
Proof.
    intros c; apply le_antisym.
    - split; simpl.
        + rewrite (cf_cont f (map_chain fst_mono c)).
          apply sup_mono; intros n; apply le_refl.
        + rewrite (cf_cont g (map_chain snd_mono c)).
          apply sup_mono; intros n; apply le_refl.
    - apply prod_sup_least; intros n; split; simpl.
        + apply cf_mono.
          exact (sup_upper (map_chain fst_mono c) n).
        + apply cf_mono.
          exact (sup_upper (map_chain snd_mono c) n).
Qed.

Definition cont_prod_map {D' E' : CPO.type}
    (f : [D →c D']) (g : [E →c E'])
    : [(D * E) →c (D' * E')] :=
  Build_cont_fun
    (mono_prod_map (cf_mono f) (cf_mono g))
    (continuous_prod_map f g).

(*
    The swap map [D×E →c E×D]: swaps the two components. 
*)
Definition cont_swap : [(D * E) →c (E * D)] :=
  cont_pair π₂ π₁.

End ProdCont.

(*
    Make the pairing notation available outside the section. 
*)
Notation "⟨ f , g ⟩" := (cont_pair f g) (at level 0, f at level 99).


(* ================================================================== *)
(*   Universal property                                               *)
(* ================================================================== *)
(*
    The product [D × E] satisfies the universal property of categorical
    products in the category of CPOs with continuous maps:

    For any CPO [C] and continuous [f : C →c D], [g : C →c E], the
    pairing [⟨f,g⟩ : C →c D×E] is the unique continuous map satisfying:
        π₁ ∘ ⟨f,g⟩ = f
        π₂ ∘ ⟨f,g⟩ = g
*)

Section ProdUniversal.
Context {D E : CPO.type}.

(* β-reduction: [π₁ ∘ ⟨f,g⟩ = f]. *)
Lemma cont_pair_fst {C : CPO.type} (f : [C →c D]) (g : [C →c E]) :
    cont_comp π₁ ⟨f,g⟩ = f.
Proof.
    apply cont_fun_eq.
    apply mono_fun_ext; intros x.
    reflexivity.
Qed.

(* β-reduction: [π₂ ∘ ⟨f,g⟩ = g]. *)
Lemma cont_pair_snd {C : CPO.type} (f : [C →c D]) (g : [C →c E]) :
    cont_comp π₂ ⟨f,g⟩ = g.
Proof.
    apply cont_fun_eq.
    apply mono_fun_ext; intros x.
    reflexivity.
Qed.

(*
    η-expansion: any [h : C →c D×E] equals [⟨π₁ ∘ h, π₂ ∘ h⟩]. 
*)
Lemma cont_pair_eta {C : CPO.type} (h : [C →c (D * E)]) :
    h = ⟨cont_comp π₁ h, cont_comp π₂ h⟩.
Proof.
    apply cont_fun_ext; intros x.
    simpl; destruct (h x); reflexivity.
Qed.

(*
    Uniqueness: if [h] satisfies the two β-laws, then [h = ⟨f,g⟩]. 
*)
Lemma cont_pair_unique {C : CPO.type} (f : [C →c D]) (g : [C →c E])
    (h : [C →c (D * E)]) :
    cont_comp π₁ h = f ->
    cont_comp π₂ h = g ->
    h = ⟨f, g⟩.
Proof.
    intros H1 H2.
    rewrite (cont_pair_eta h), H1, H2.
    reflexivity.
Qed.

(*
    Functoriality of pairing: [⟨f∘k, g∘k⟩ = ⟨f,g⟩ ∘ k]. 
*)
Lemma cont_pair_comp {C C' : CPO.type}
    (f : [C' →c D]) (g : [C' →c E]) (k : [C →c C']) :
    ⟨cont_comp f k, cont_comp g k⟩ = cont_comp ⟨f, g⟩ k.
Proof.
    apply cont_fun_ext; intros x.
    reflexivity.
Qed.

(*
    [⟨π₁, π₂⟩ = id] (the pairing of the two projections is the identity). 
*)
Lemma cont_pair_id : ⟨π₁, π₂⟩ = cont_id (D * E).
Proof.
    apply cont_fun_ext; intros x.
    simpl; destruct x; reflexivity.
Qed.

End ProdUniversal.


(* ================================================================== *)
(*   PointedCPO product                                               *)
(* ================================================================== *)
(*
    If [D] and [E] are pointed CPOs, so is [D × E], with [⊥ = (⊥, ⊥)].
*)

Section ProdPointed.
Context {D E : PointedCPO.type}.

Definition prod_bottom : D * E := (⊥, ⊥).

Lemma prod_bottom_least (p : D * E) : prod_bottom ⊑ p.
Proof.
    exact (conj (bottom_least (fst p)) (bottom_least (snd p))).
Qed.

End ProdPointed.

HB.instance Definition prod_HasBottom {D E : PointedCPO.type} :=
    HasBottom.Build (D * E) prod_bottom.

HB.instance Definition prod_IsPointed {D E : PointedCPO.type} :=
    IsPointed.Build (D * E) prod_bottom_least.

(*
    The bottom of the product computes as expected. 
*)
Lemma prod_bottom_eq {D E : PointedCPO.type} :
    (⊥ : D * E) = (⊥, ⊥).
Proof.
    reflexivity.
Qed.

(*
    The projections send the product bottom to the factor bottoms. 
*)
Lemma fst_bottom {D E : PointedCPO.type} :
    fst (⊥ : D * E) = (⊥ : D).
Proof.
    reflexivity.
Qed.

Lemma snd_bottom {D E : PointedCPO.type} :
    snd (⊥ : D * E) = (⊥ : E).
Proof.
    reflexivity.
Qed.


(* ================================================================== *)
(*  Miscellaneous derived lemmas                                       *)
(* ================================================================== *)

Section ProdMisc.
Context {D E : CPO.type}.

(*
    The product order is equivalent to coordinatewise comparison.
    (Unfolding [⊑] on [D * E] always gives a conjunction.) 
*)
Lemma prod_le_iff (p q : D * E) :
    p ⊑ q <-> fst p ⊑ fst q /\ snd p ⊑ snd q.
Proof.
    reflexivity.
Qed.

(*
    The sup of a constant chain in [D * E] is the constant value.
    (Follows from [sup_const_chain] on each component.) 
*)
Lemma prod_sup_const (p : D * E) :
    ⊔ (const_chain p) = p.
Proof.
    exact (sup_const_chain p).
Qed.

(*
    Sup of a product chain is monotone in the pointwise bound:
    if [c ⊑ d] pointwise, then [⊔ c ⊑ ⊔ d].
    (Immediate from [sup_mono] on each component.) 
*)
Lemma prod_sup_mono (c d : chain (D * E)) :
    (forall n, c.[n] ⊑ d.[n]) ->
    ⊔ c ⊑ ⊔ d.
Proof.
    intros Hle; split.
    - apply sup_mono; intros n; exact (proj1 (Hle n)).
    - apply sup_mono; intros n; exact (proj2 (Hle n)).
Qed.

(*
    Extensionality for product chains: if two chains agree pointwise,
    they have the same sup. 
*)
Lemma prod_sup_ext (c d : chain (D * E)) :
    (forall n, c.[n] = d.[n]) -> ⊔ c = ⊔ d.
Proof.
    intros Heq; exact (sup_ext c d Heq).
Qed.

(*
    Pairing commutes with sup:
    [⟨f,g⟩(⊔ c) = (f(⊔ c), g(⊔ c))]. 
*)
Lemma cont_pair_sup {C : CPO.type} (f : [C →c D]) (g : [C →c E])
    (c : chain C) :
    (⟨f, g⟩ : [C →c (D * E)]) (⊔ c) = (f (⊔ c), g (⊔ c)).
Proof.
    reflexivity.
Qed.

End ProdMisc.
Close Scope type_scope.