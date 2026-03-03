(*  CPO Structures

    ω-Complete partial orders (CPOs) and pointed CPOs, declared using the
    Hierarchy Builder (HB) packed-class framework.

    This is [src/structures/CPO.v].  Only structure _declarations_ live
    here.  Derived theory (Scott continuity, Kleene fixed point theorem,
    admissibility, etc.) belongs in [src/theory/CPOTheory.v] and
    [src/theory/FixedPoints.v].  Concrete instances ([nat], [lift], product,
    function space, ...) belong in [src/instances/].

    Imports:
      [src/structures/Order.v] — Preorder, PartialOrder, chain, mono_fun

    Phase coverage:
      Phase 0 — HasSup, IsCPO, CPO
                HasBot, IsPointed, PointedCPO

    Reference:
      Abramsky & Jung, "Domain Theory" (1994), Definition 2.1.13:
      "A *poset* D in which every directed subset has a supremum we call
      a directed-complete partial order, or dcpo for short."
      A poset (Definition 2.1.1) includes antisymmetry, so CPO is built
      on [PartialOrder], not merely [Preorder].

      https://ncatlab.org/nlab/show/dcpo
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order.

(* ------------------------------------------------------------------ *)
(*    §1  Suprema of ω-chains                                         *)
(* ------------------------------------------------------------------ *)
(*
    [HasSup] equips a type [T] with a function [sup] that assigns a
    candidate least-upper-bound to every ω-chain in [T].

    We use [chain T] (from [Order.v]) rather than [nat -> T] so that the
    monotonicity invariant is always baked in. 

    [HasSup] sits above [PartialOrder] because CPOs are by definition
    built on posets — a poset includes antisymmetry
    (Abramsky & Jung §2.1.1, §2.1.5).
*)
HB.mixin Record HasSup T of PartialOrder T := {sup : chain T -> T}.
HB.structure Definition Sup := {T & HasSup T}.
Notation "⊔ c" := (sup c) (at level 35, right associativity).


(* ------------------------------------------------------------------ *)
(*  §2  The CPO axioms                                                *)
(* ------------------------------------------------------------------ *)
(* 
    [IsCPO] asserts that [sup] is genuinely the _least_ upper bound of
    every ω-chain:

    - [sup_upper]:  each element of [c] is ⊑ [⊔ c]  (upper bound)
    - [sup_least]:  if [x] is any upper bound of [c], then [⊔ c ⊑ x]
                    (least among upper bounds)

    Together these two axioms uniquely characterise the supremum: if [s]
    and [s'] are both least upper bounds of [c] then [s = s'] by
    antisymmetry. 
*)
HB.mixin Record IsCPO T of HasSup T & PartialOrder T := {
  sup_upper : forall (c : chain T) (n : nat), c.[n] ⊑ ⊔ c;
  sup_least : forall (c : chain T) (x : T),
                (forall (n : nat), c.[n] ⊑ x) -> ⊔ c ⊑ x;
}.

(* 
DOCS: 
    The bundled [CPO] structure: a type with [Preorder], [HasSup], and
    [IsCPO].  Any [CPO.type] is automatically a [Preorder.type]. 
*)
HB.structure Definition CPO := {T of PartialOrder T & HasSup T & IsCPO T}.
Notation "CPO.type" := CPO.type (only parsing).


(* ------------------------------------------------------------------ *)
(*   §3  Basic derived facts (immediate consequences of the axioms)   *)
(* ------------------------------------------------------------------ *)

(* 
    Suprema are monotone with respect to pointwise chain ordering.
    (If [c.[n] ⊑ d.[n]] for all [n] then [⊔ c ⊑ ⊔ d].)
    This is proved here rather than in [CPOTheory.v] because it is
    immediate from the axioms and used in many downstream definitions. 
*)
Lemma sup_mono {T : CPO.type} (c d : chain T) : 
  (forall n, c.[n] ⊑ d.[n]) -> ⊔ c ⊑ ⊔ d.
Proof.
  intros Hle.
  apply sup_least.
  intro n.
  apply le_trans with (d.[n]).
  - apply Hle.
  - apply sup_upper.
Qed.

(* 
    Two chains with the same underlying function have the same sup.
    Useful when constructing chains by rewriting. 
*)
Lemma sup_ext {T : CPO.type} (c d : chain T) :
  (forall n, c.[n] = d.[n]) -> ⊔ c = ⊔ d.
Proof.
  intro Heq.
  apply le_antisym;
  apply sup_least; intro n; [rewrite Heq | rewrite <- Heq]; apply sup_upper. 
Qed.


(* ------------------------------------------------------------------ *)
(*   §4  Pointed CPOs                                                 *)
(* ------------------------------------------------------------------ *)
(* 
    [HasBot] equips a type with a distinguished element [bot] (written [⊥]).
    This is kept separate from [IsCPO] so that non-pointed CPOs (which are
    perfectly valid) are not forced to carry a bottom element. 
*)
HB.mixin Record HasBottom T of HasLe T:= {bottom : T}.
HB.structure Definition Bottom := {T & HasBottom T}.
Notation "⊥" := bottom (at level 0).

(* [IsPointed] asserts that [bottom] is the least element of the CPO. *)
HB.mixin Record IsPointed T of CPO T & HasBottom T := {
  bottom_least : forall (x : T), ⊥ ⊑ x;
}.


(*
    The bundled [PointedCPO] structure: a [CPO] that also has a least
    element.  Any [PointedCPO.type] is automatically a [CPO.type] and a
    [Preorder.type]. 
*)
HB.structure Definition PointedCPO := {T of CPO T & HasBottom T & IsPointed T}.
Notation "PointedCPO.type" := PointedCPO.type (only parsing).


(* ------------------------------------------------------------------ *)
(*  §5  Continuous functions (predicate only)                         *)
(* ------------------------------------------------------------------ *)
(* 
    The _predicate_ [continuous] is declared here so that [Morphisms.v]
    can build on it without depending on [CPOTheory.v].  The [cont_fun]
    record and all substantive lemmas live in [src/structures/Morphisms.v]
    and [src/theory/CPOTheory.v] respectively.

    A monotone function [f : mono_fun D E] between CPOs is _Scott
    continuous_ if it commutes with all ω-chain suprema:
      [f (⊔ c) = ⊔ (map_chain f c)]

    Note: the equality here is in [E], which may merely be a preorder.
    In a partial order, [sup_upper] and [sup_least] uniquely determine
    [⊔], so the equality follows from the two inequalities; in a plain
    preorder it must be stated as propositional equality (or as mutual
    [⊑]).  We use propositional equality [=] throughout Phase 0 and
    revisit this in Phase 1 when working in an enriched setting. 
*)
Definition continuous {D E : CPO.type} (f : mono_fun D E) :=
  forall (c : chain D), f (⊔ c) = ⊔ (map_chain f c).


(* ------------------------------------------------------------------ *)
(*  Notes for later phases                                           *)
(* ------------------------------------------------------------------ *)
(*
   Phase 0/1 (FunctionSpaces.v):
     [mono_fun P Q] will be migrated to an HB structure with carrier
     [P -> Q] and registered as a [CPO.type] under the pointwise order.
     At that point [cont_fun] should similarly become an HB structure so
     that the exponential CPO [D ⇒ E] arises by canonical inference.

   Phase 1 (Enriched.v):
     The enriched-hom mixin will extend [CPO.type] with a hom-object
     functor valued in [CPO], giving locally continuous categories.

   Phase 2 (quantum/qCPO.v):
     Quantum CPOs replace the underlying [Prop]-valued order with an
     order valued in a quantale; [HasSup] will be revisited at that point.
*)