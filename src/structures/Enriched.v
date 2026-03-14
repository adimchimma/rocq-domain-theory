(** * Enriched

    Phase 1: Enriched category structures.

    Definitions to be added:
    - [IsEnriched]: a category whose hom-sets are CPOs and whose composition
      is a continuous bifunctor.
    - [IsLocallyContinuous]: functors between enriched categories that act
      continuously on each hom-object.
    - Basic laws: associativity, identity, and continuity of composition.
*)

(** * CPO-Enriched Category Structures

    A category enriched over [CPO] is one in which every hom-set is a
    CPO, and composition is a Scott-continuous operation.

    This is [src/structures/Enriched.v].  Only structure _declarations_
    live here.  Proofs about enriched natural transformations, locally
    continuous functors, and the limit-colimit coincidence belong in
    [src/theory/EnrichedTheory.v] and [src/theory/NatTrans.v].

    Imports:
      [src/structures/Order.v]     — Preorder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, continuous
      [src/structures/Morphisms.v] — cont_fun, cont_comp, cont_id

    Phase coverage:
      Phase 1 — HasHom, HasId
                IsCPOEnriched, CPOEnrichedCat
                HasEndo, IsLocallyContinuous, LocallyContinuousFunctor
                HasMixedEndo  (data only; axioms in DomainEquations.v)

    ** Core definitions and their sources **

    [CPOEnrichedCat]:
      Abramsky & Jung §5.2.2 (preamble to Definition 5.2.3).  The
      canonical example is CPO itself, where Hom(D,E) = [D → E] with
      the pointwise order (A&J §3.2.2).
      Also: Kornell-Lindenhovius-Mislove (2024) §3.3, Theorem 3.3.5,
      which proves qCPO is enriched over CPO by showing composition is
      separately continuous in each variable (Lemmas 3.3.3–3.3.4).

    [LocallyContinuousFunctor]:
      Abramsky & Jung Definition 5.2.3:
      "A functor F from D to E is called *locally continuous*, if the
      maps Hom(D, D') → Hom(F(D), F(D')), f ↦ F(f), are continuous
      for all objects D and D' from D."

    [HasMixedEndo]:
      Abramsky & Jung Definition 5.2.5 (mixed-variance locally
      continuous bifunctor F : D^op × D' → E).
      Benton-Kennedy-Varming (2009) §4, [BiFunctor] record:
        ob  : cpo → cpo → cpo
        mor : ∀ (A B C D), (B ⇒c A) × (C ⇒c D) ⇒c (ob A C ⇒c ob B D)
      Our [MF_obj]/[MF_mor] follow this exactly.

    ** Design note: separate vs joint continuity **

    A&J Lemma 3.2.6 states: a function f : D × E → F between DCPOs is
    (jointly) Scott-continuous if and only if it is separately continuous
    in each variable.  This has two consequences for our axioms:

    (1) In [IsCPOEnriched], requiring [comp_cont_l] and [comp_cont_r]
        (separate Scott-continuity of composition in each argument) is
        equivalent to requiring joint Scott-continuity of composition as
        a map Hom(A,B) × Hom(B,C) → Hom(A,C).  We choose the separate
        form to avoid a dependency on Products.v (which would be circular
        at this stage of the build).

    (2) In [IsMixedLocallyContinuous] (deferred to DomainEquations.v),
        the A&J §5.2.5 joint condition
          F(⊔A, ⊔A') = ⊔_{f∈A, f'∈A'} F(f,f')
        is equivalent to separate continuity in each argument by the same
        lemma, and that is the form we will axiomatise.
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO Morphisms.

(* ------------------------------------------------------------------ *)
(*   The data of a CPO-enriched category                              *)
(* ------------------------------------------------------------------ *)
(* 
    [HasHom] equips a type [Obj] of objects with a family of hom-CPOs.
    For every pair [A B : Obj], [hom A B] is a [CPO.type].

    Design note: [Obj] is the HB carrier.  HB normally equips a type
    with algebraic structure, and here [Obj] plays the role of the type
    of objects of a category.  Each subsequent mixin adds categorical
    data or axioms indexed by [Obj]. 
*)
HB.mixin Record HasHom (Obj : Type) := {hom : Obj -> Obj -> CPO.type}.
HB.structure Definition Hom := {Obj & HasHom Obj}.
HB.mixin Record HasId Obj of HasHom Obj := {
  id_mor : forall (A : Obj), hom A A;
}.
HB.structure Definition Id_Mor := {Obj of HasHom Obj & HasId Obj}.


(* ------------------------------------------------------------------ *)
(*   CPO-enrichment axioms                                            *)
(* ------------------------------------------------------------------ *)
(* 
  [IsCPOEnriched] bundles the data and axioms of a CPO-enriched category:

    Composition [comp] is included directly in this mixin rather than in a
    separate [HasComp] mixin, because HB's global structure projection for
    [comp] requires canonical-structure resolution on the carrier type.
    Inside a mixin body the carrier [Obj] is a plain [Type] — not yet a
    packed structure — so the global projection cannot fire.  Placing
    [comp] as a local field avoids this entirely.

    (a) Composition is Scott-continuous in each argument separately.
        By A&J Lemma 3.2.6 this is equivalent to joint continuity of
          comp : Hom(A,B) × Hom(B,C) → Hom(A,C).
        We choose the separate form to avoid a dependency on Products.v.
        See also Kornell-Lindenhovius-Mislove §3.3 Lemmas 3.3.3–3.3.4
        and Theorem 3.3.5 for the same proof strategy applied to qCPO.

    (b) Monotonicity fields precede continuity fields.  The [continuous]
        predicate (from Morphisms.v) takes a [mono_fun] as argument,
        which in turn requires a proof of monotonicity.  Placing
        [comp_mono_*] before [comp_cont_*] ensures [Build_mono_fun]
        below has a proof in scope.

    (c) Categorical laws use Leibniz equality [=].  If the underlying
        CPO type uses a setoid equality [==], restate the laws in
        [EnrichedTheory.v] using that relation.

    Notation [f ⊚ g] is defined *after* the [CPOEnrichedCat] structure
    so that outside the mixin it resolves through the global projection.
*)
HB.mixin Record IsCPOEnriched Obj of HasHom Obj & HasId Obj := {
  (* --- composition data --- *)

  (*
    Composition, written in diagrammatic order: [comp f g] means
    "first [g], then [f]", consistent with [cont_comp] in [Morphisms.v].
    That is, [comp f g : hom A C] when [f : hom B C] and [g : hom A B].
  *)
  comp : forall {A B C : Obj}, hom B C -> hom A B -> hom A C;

  (* --- monotonicity (must precede continuity fields) --- *)

  (* 
    Post-composition with [f] is monotone:
      [g ≤ g'] implies [comp f g ≤ comp f g']. 
  *)
  comp_mono_l : forall {A B C : Obj} (f : hom B C),
    monotone (hom A B) (hom A C) (fun g => comp f g);

  (* 
    Pre-composition with [g] is monotone:
      [f ≤ f'] implies [comp f g ≤ comp f' g]. 
  *)
  comp_mono_r : forall {A B C : Obj} (g : hom A B),
    monotone (hom B C) (hom A C) (fun f => comp f g);
  

  (* --- Scott continuity --- *)
  
  (*
    Post-composition with [f] is Scott-continuous:
      [comp f (⊔ chn) = ⊔_n (comp f (chn n))].
  *)
  comp_cont_l : forall {A B C : Obj} (f : hom B C),
    @continuous (hom A B) (hom A C)
        (Build_mono_fun (fun (g : hom A B) => comp f g) (comp_mono_l f));
  
  (*
    Pre-composition with [g] is Scott-continuous:
      [comp (⊔ chn) g = ⊔_n (comp (chn n) g)].
  *)
  comp_cont_r : forall {A B C : Obj} (g : hom A B),
    @continuous (hom B C) (hom A C)
        (Build_mono_fun (fun (f : hom B C) => comp f g) (comp_mono_r g));
  
  
  (* --- categorical laws --- *)

  (* Left identity: [comp (id_mor B) f = f]. *)
  comp_id_l : forall {A B : Obj} (f : hom A B),
    comp (id_mor B) f = f;
  
  (** Right identity: [comp f (id_mor A) = f]. *)
  comp_id_r : forall {A B : Obj} (f : hom A B),
    comp f (id_mor A) = f;
  
  (* Associativity: [comp (comp h g) f = comp h (comp g f)]. *)
  comp_assoc : forall {A B C D : Obj}
    (h : hom C D) (g : hom B C) (f : hom A B),
        comp (comp h g) f = comp h (comp g f);
}.

HB.structure Definition CPOEnrichedCat := {Obj of HasHom Obj & HasId Obj & IsCPOEnriched Obj}.
Notation "f ⊚ g" := (comp _ _ _ f g) (at level 40, left associativity).

Notation "CPOEnrichedCat.type" := CPOEnrichedCat.type (only parsing).


(* ------------------------------------------------------------------ *)
(*   Packaged composition as cont_fun                                 *)
(* ------------------------------------------------------------------ *)
(*
    Package post- and pre-composition as [cont_fun]s.  These are the
    form expected by lemmas in [Morphisms.v] and will be needed in
    [EnrichedTheory.v] when constructing natural transformations. 
*)
Definition comp_l_cont_fun {C : CPOEnrichedCat.type} {A B D : C}
  (f : hom D B) : [(hom A D) →c (hom A B)] :=
      Build_cont_fun
        (Build_mono_fun (fun (g : hom A D) => f ⊚ g) (comp_mono_l A D B f))
        (comp_cont_l A D B f).

Definition comp_r_cont_fun {C : CPOEnrichedCat.type} {A B D : C}
  (g : hom A D) : [(hom D B) →c (hom A B)] :=
      Build_cont_fun
        (Build_mono_fun (fun (f : hom D B) => f ⊚ g) (comp_mono_r _ _ _ g))
        (comp_cont_r _ _ _ g).


(* ------------------------------------------------------------------ *)
(*   Locally continuous covariant endofunctors                        *)
(* ------------------------------------------------------------------ *)
(*
    An endofunctor on a [CPOEnrichedCat] consists of:
    - [F_obj]: action on objects
    - [F_mor]: action on morphisms (a family of functions between hom-CPOs)

    We separate the data ([HasEndo]) from the axioms
    ([IsLocallyContinuous]) per the HB discipline. 
*)
HB.mixin Record HasEndo (Obj : Type) of HasHom Obj := {
  F_obj : Obj -> Obj;
  F_mor : forall {A B : Obj}, hom A B -> hom (F_obj A) (F_obj B);
}.
HB.structure Definition F_Obj := {Obj of HasHom Obj & HasEndo Obj}.

(* 
    [IsLocallyContinuous] axiomatises:
    - Local continuity (A&J Definition 5.2.3): for each pair of objects
      A, B, the map [F_mor : Hom(A,B) → Hom(F(A),F(B))] is Scott-
      continuous.
    - Functoriality: [F_mor] preserves identity and composition.

    Monotonicity is stated before continuity for the same reason as in
    [IsCPOEnriched]: [Build_mono_fun] needs a proof in scope.

    Note: A&J Proposition 5.2.4 states that a locally continuous functor
    restricts to a continuous functor on the subcategory of embeddings.
    This is proved in [EnrichedTheory.v]. 
*)
HB.mixin Record IsLocallyContinuous Obj of CPOEnrichedCat Obj & HasEndo Obj := {

  (* 
      [F_mor] is monotone on each hom-CPO:
      [f ⊑ g] in [Hom(A,B)] implies [F_mor f ⊑ F_mor g]
      in [Hom(F(A),F(B))].

      Inside the mixin body, HB makes all originally-implicit record
      field arguments explicit.  So the local [F_mor] binding has type
        [forall (A B : Obj), hom A B -> hom (F_obj A) (F_obj B)]
      and must be applied as [F_mor A B] (not bare [F_mor]).
      We eta-expand with [fun h => F_mor A B h] so that [monotone]
      and [Build_mono_fun] see the right function type directly.
  *)
  F_mor_mono : forall {A B : Obj},
      monotone (hom A B) (hom (F_obj A) (F_obj B))
        (fun h => F_mor A B h) ;

  (* 
      [F_mor] is Scott-continuous on each hom-CPO.
      This is exactly A&J Definition 5.2.3:
        F(⊔_n f_n) = ⊔_n F(f_n)  in Hom(F(A), F(B)). 
  *)
  F_mor_cont : forall {A B : Obj},
      @continuous (hom A B) (hom (F_obj A) (F_obj B))
        (@Build_mono_fun (hom A B) (hom (F_obj A) (F_obj B))
          (fun h => F_mor A B h) (F_mor_mono)) ;

  (* Preservation of identity: [F_mor (id_mor A) = id_mor (F_obj A)]. *)
  F_mor_id : forall (A : Obj),
      F_mor A A (id_mor A) = id_mor (F_obj A) ;

  (* Preservation of composition:
      [F_mor (comp f g) = comp (F_mor f) (F_mor g)]. *)
  F_mor_comp : forall {A B C : Obj} (f : hom B C) (g : hom A B),
      F_mor A C (comp A B C f g) =
        comp (F_obj A) (F_obj B) (F_obj C) (F_mor B C f) (F_mor A B g) ;
}.

HB.structure Definition LocallyContinuousFunctor :=
  { Obj of CPOEnrichedCat Obj & HasEndo Obj & IsLocallyContinuous Obj }.
Notation "LocallyContinuousFunctor.type" :=
  LocallyContinuousFunctor.type (only parsing).

(* Package [F_mor] as a [cont_fun] for use with [Morphisms.v]. *)
Definition F_mor_cont_fun {C : LocallyContinuousFunctor.type} {A B : C}
    : [(hom A B) →c (hom (F_obj A) (F_obj B))] :=
  Build_cont_fun
    (Build_mono_fun (fun H => F_mor A B H) (F_mor_mono _ _))
    (F_mor_cont A B).


(* ------------------------------------------------------------------ *)
(*   Mixed-variance bifunctors (data; axioms in DomainEquations)      *)
(* ------------------------------------------------------------------ *)
(* 
    For recursive domain equations [X ≅ F(X, X)] where [F] is
    contravariant in its first argument and covariant in its second
    (A&J §5.2, Definition 5.2.5), we need a mixed-variance bifunctor.

    ** Object part **
    [MF_obj : Obj -> Obj -> Obj] assigns to each pair (A, B) the object
    F(A, B).  This corresponds to Benton-Kennedy-Varming's [ob : cpo → cpo → cpo].

    ** Morphism part **
    The action on morphisms is:
      Given  [f : hom A2 A1]   (contravariant: "backwards" in 1st arg)
      and    [g : hom B1 B2]   (covariant:     "forwards"  in 2nd arg)
      produce [MF_mor f g : hom (MF_obj A1 B1) (MF_obj A2 B2)].

    This corresponds to Benton-Kennedy-Varming's:
      [mor : ∀ (A B C D), (B ⇒ c A) × (C ⇒ c D) ⇒c (ob A C ⇒ c ob B D)]

    and implements A&J Definition 5.2.5's condition (in its bilinear form)
    that for directed sets A ⊆ Hom(D2,D1) and A' ⊆ Hom(D'1,D'2):
      F(⊔A, ⊔A') = ⊔_{f ∈ A, f' ∈ A'} F(f, f')  in Hom(F(D1,D'1), F(D2,D'2)).

    The full axioms — functoriality, monotonicity and Scott-continuity in
    each variable — are deferred to [src/theory/DomainEquations.v], where
    the bilimit construction over the diagonal X ↦ F(X,X) is developed.
    We record only the data here so that [DomainEquations.v] can build its
    [IsMixedLocallyContinuous] mixin on top of [HasMixedEndo]. 
*)
HB.mixin Record HasMixedEndo (Obj : Type) of HasHom Obj := {
  (** Object action: [MF_obj A B] is the object [F(A, B)]. *)
  MF_obj : Obj -> Obj -> Obj ;

  (** Morphism action: contravariant in the first argument, covariant in
      the second.
        [f : A2 → A1]   (contravariant)
        [g : B1 → B2]   (covariant)
      gives  [MF_mor f g : F(A1,B1) → F(A2,B2)]. *)
  MF_mor : forall {A1 A2 B1 B2 : Obj},
      hom A2 A1 ->    (* contravariant in first argument  *)
      hom B1 B2 ->    (* covariant    in second argument  *)
      hom (MF_obj A1 B1) (MF_obj A2 B2) ;
}.
HB.structure Definition MF_Obj :=
  {Obj of CPOEnrichedCat Obj & HasMixedEndo Obj}.

(** Axioms to be added in [DomainEquations.v] over [HasMixedEndo]:
      - [MF_mor_id]    : [MF_mor (id A) (id B) = id (MF_obj A B)]
      - [MF_mor_comp]  : bifunctoriality
                         [MF_mor (f' ∘ f) (g ∘ g')
                          = MF_mor f g ∘ MF_mor f' g']
                         (contravariant composition reverses, covariant
                          composition preserves direction)
      - [MF_mor_mono_l]: [f ≤ f'] in Hom(A2,A1) implies
                         [MF_mor f g ≤ MF_mor f' g]
      - [MF_mor_mono_r]: [g ≤ g'] in Hom(B1,B2) implies
                         [MF_mor f g ≤ MF_mor f g']
      - [MF_mor_cont_l]: Scott-continuous in first argument (fixing g)
      - [MF_mor_cont_r]: Scott-continuous in second argument (fixing f)
    Together [MF_mor_cont_l] and [MF_mor_cont_r] are equivalent by A&J
    Lemma 3.2.6 to the joint continuity condition in A&J Definition 5.2.5.
*)


(* ------------------------------------------------------------------ *)
(*   Instance checkpoint                                              *)
(* ------------------------------------------------------------------ *)
(*
   Phase 1 instance registrations (deferred to [src/instances/]):

   [Function.v]:
     Register [CPO.type] as a [CPOEnrichedCat] with:
       [hom D E     := fun_cpo D E]   (pointwise function-space CPO)
       [id_mor      := cont_id]
       [comp        := cont_comp]
     Verify [comp_cont_l] and [comp_cont_r] using the pointwise
     order on continuous function spaces (A&J §3.2.2).

   [DomainEquations.v]:
     - Define [IsMixedLocallyContinuous] over [HasMixedEndo].
     - Construct the bilimit of a locally continuous functor.
     - Prove it is the canonical solution to [X ≅ F(X)] / [X ≅ F(X,X)].
     - Derive the key instance [D ≅ [D → D]⊥] as a corollary.
*)