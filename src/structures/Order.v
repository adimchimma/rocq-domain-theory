(*  Order Structures

    Preorders, partial orders, chains, and monotone functions, declared
    using the Hierarchy Builder (HB) packed-class framework.

    This is [src/structures/Order.v].  Only structure _declarations_ live
    here; proofs and derived constructions belong in [src/theory/OrderTheory.v]
    and [src/instances/].

    Dependency chain (nothing imported from this project):
      Rocq stdlib + HB

    Phase coverage:
      Phase 0 — HasLe, IsPreorder, IsPartialOrder, chain, mono_fun
    
    Reference:
      https://en.wikipedia.org/wiki/Partially_ordered_set
      https://people.maths.ox.ac.uk/bays/teaching/3u03/notes/8-porders.pdf  
*)

From HB Require Import structures.

(* ------------------------------------------------------------------ *)
(*  §1  The order relation                                           *)
(* ------------------------------------------------------------------ *)
(*  
    [HasLe] attaches a binary relation [le] to a type [T].
    No axioms yet — we add those in [IsPreorder]. 
*)
HB.mixin Record HasLe (T : Type) := {leT : T -> T -> Prop}.
HB.structure Definition Le := {T & HasLe T}.

(* 
DOCS.Notation: 
    The bracketed form [x ⊑[T] y] pins the carrier when Rocq cannot infer it from context. 
*)
Notation "x ⊑ y" := (leT x y) (at level 70, no associativity).
Notation "x ⊑[ T ] y" := (@leT T _ x y)
                            (at level 70, no associativity, only parsing).


(* ------------------------------------------------------------------ *)
(*   §2  Preorders                                                    *)
(* ------------------------------------------------------------------ *)
(* [IsPreorder] adds reflexivity and transitivity to [HasLe]. *)
HB.mixin Record IsPreorder T of HasLe T := {
    le_refl : forall (x : T), x ⊑ x;
    le_trans : forall (x y z : T), x ⊑ y -> y ⊑ z -> x ⊑ z;
}.

(*  
DOCS.rocq:
    The bundled [Preorder] structure: a type equipped with [HasLe] and
    [IsPreorder].  Instances of [Preorder.type] can be used wherever a
    type is expected (via the coercion [Preorder.sort]). 
*)
HB.structure Definition Preorder := {T of HasLe T & IsPreorder T}.
Notation "Preorder.type" := Preorder.type (only parsing).

(* 
DOCS.order-theory:
    Preorder-level equivalence:
        In a preorder that is not yet a partial order, [x ≈ y] means [x ⊑ y]
        and [y ⊑ x].  This is sometimes called the _kernel_ of the preorder.
*)
Definition pequiv {T : Preorder.type} (x y : T) : Prop :=
    x ⊑ y /\ y ⊑ x.

Notation "x ≈ y" := (pequiv x y) (at level 70, no associativity).
Notation "x ≈[ T ] y" := (@pequiv T x y)
                            (at level 70, no associativity, only parsing).


(* ------------------------------------------------------------------ *)
(*  §3  Partial orders                                                *)
(* ------------------------------------------------------------------ *)
(* [IsPartialOrder] adds antisymmetry: equivalent elements are equal. *)
HB.mixin Record IsPartialOrder T of Preorder T := {
    le_antisym : forall (x y : T), x ⊑ y -> y ⊑ x -> x = y;
}.

HB.structure Definition PartialOrder := {T of Preorder T & IsPartialOrder T}.
Notation "PartialOrder.type" := PartialOrder.type (only parsing).


(* ------------------------------------------------------------------ *)
(*   §4  ω-Chains                                                     *)
(* ------------------------------------------------------------------ *)
(* 
DOCS.order-theory: 
    An [ω-chain] in a preorder is a _monotone_ sequence indexed by [nat].
    Monotonicity ([ch_mono]) is what distinguishes a chain from an
    arbitrary ω-sequence, and is the key notion for ω-CPOs.

    We keep [chain] as a plain [Record] parameterised over [Preorder.type]
    rather than a second HB hierarchy, because chains are not themselves
    carriers of new structure — they are _data_ built on top of a given
    preorder.  Downstream files that need to quantify over chains simply
    take [c : chain P] for [P : Preorder.type].
*)
Record chain (P : Preorder.type) : Type := Build_chain {
    ch : nat -> P;
    ch_mono : forall (m n : nat), m <= n -> ch m ⊑ ch n;
}.

Arguments Build_chain {P} ch ch_mono.
Arguments ch {P} c n.
Arguments ch_mono {P} c m n _.

Notation "c .[ n ]" := (ch c n) (at level 9, format "c .[ n ]").


Lemma chain_succ_le {P : Preorder.type} (c : chain P) (n : nat) :
    c.[n] ⊑ c.[S n].
Proof.
    apply ch_mono.
    apply le_S.
    apply le_n.
Qed.


(* Various chain Constructions *)

(* The constant chain at a point [x] *)
Definition const_chain {P : Preorder.type} (x : P) : chain P :=
    Build_chain (fun _ => x) (fun _ _ _ => le_refl x).

(* The tail of a chain *)
Definition tail_chain {P : Preorder.type} (c : chain P) : chain P := 
    Build_chain (fun n => c.[S n])
                (fun m n HmLEn => ch_mono c (S m) (S n) (le_n_S _ _ HmLEn)).


(* ------------------------------------------------------------------ *)
(*   §5  Monotone functions                                           *)
(* ------------------------------------------------------------------ *)
(* A function [f : P -> Q] between preorders is [monotone] if it preserves [⊑]. *)
Definition monotone (P Q : Preorder.type) (f : P -> Q) : Prop :=
    forall (x y : P), x ⊑ y -> f x ⊑ f y.

(* 
    Note on HB migration:
        [FunctionSpaces.v] already registers [[D →c E]] as a CPO via
        HB instances without converting [mono_fun] to a Funclass-keyed
        HB structure.  A full migration would touch 50+ call sites for
        limited gain; revisit in Phase 2 if enriched-hom composability
        demands it.  See also [Morphisms.v] header note.
*)
Record mono_fun (P Q : Preorder.type) : Type := Build_mono_fun {
    mf_fun :> P -> Q;
    mf_mono : monotone P Q mf_fun;
}.

Arguments Build_mono_fun {P Q} mf_fun mf_mono.
Arguments mf_fun {P Q} f x : rename.
Arguments mf_mono {P Q} f x y _ : rename.

(* Applying a chain to a monotone function returns a chain *)
Definition map_chain {P Q : Preorder.type} (f : mono_fun P Q) (c : chain P) 
    : chain Q := 
        Build_chain (fun n => f c.[n])
                    (fun m n HmLEn => mf_mono f c.[m] c.[n] (ch_mono c m n HmLEn)).

(* Identity and composition *)
Definition mono_id (P : Preorder.type) : mono_fun P P :=
    Build_mono_fun (fun x => x) (fun _ _ HmLEn => HmLEn).

Definition mono_comp {P Q R : Preorder.type} 
    (g : mono_fun Q R) (f : mono_fun P Q) : mono_fun P R :=
        Build_mono_fun (fun x => g (f x))
                       (fun x y HxLEy => mf_mono g _ _ (mf_mono f x y HxLEy)).

(* Categorical laws (proved by [reflexivity] because the definitions compute definitionally) *)
Lemma mono_comp_assoc {P Q R S : Preorder.type}
    (h : mono_fun R S) (g : mono_fun Q R) (f : mono_fun P Q) :
    mono_comp h (mono_comp g f) = mono_comp (mono_comp h g) f.
Proof.
    reflexivity.
Qed.

Lemma mono_comp_id_l {P Q : Preorder.type} (f : mono_fun P Q) :
    mono_comp f (mono_id P) = f.
Proof.
    destruct f; reflexivity.
Qed.

Lemma mono_comp_id_r {P Q : Preorder.type} (f : mono_fun P Q) :
    mono_comp (mono_id Q) f = f.
Proof.
    destruct f; reflexivity.
Qed.