(*  QuantumStructure — Involutive Quantales and Quantum Posets

    Phase 2: Algebraic structures for quantum domain theory.

    This is [src/quantum/QuantumStructure.v].  It provides the base
    algebraic structures needed by the quantum portion of the library:

    Contents:
      §1  Descending ω-chains    — dual of [chain] from Order.v
      §2  Quantale operations    — [HasQuantaleOps] mixin
      §3  Involutive quantale    — [IsInvQuantale] axioms, [InvQuantale]
      §4  Notation               — ⊗ for product, ⊓ for meet
      §5  Kronecker delta        — [q_delta], the identity relation in Q
      §6  Quantum posets         — [qposet] record (Type + Q-valued order)
      §7  Derived properties     — [qp_antitone_l] from transitivity

    Design decision (DD-022):
      The quantale Q is an HB structure ([InvQuantale]) building on
      [PartialOrder] from Order.v.  Quantum posets are plain Records
      parametrized by Q, following the pattern of [chain] and
      [mono_fun] in Order.v — they are data built on a given structure,
      not carriers of new HB structure.

      This avoids the HB limitation around structures parametrized by
      other structures.

    Imports:
      [src/structures/Order.v] — HasLe, IsPreorder, IsPartialOrder, chain

    Phase coverage:
      Phase 2 — desc_chain, InvQuantale, qposet

    References:
      KLM (2024) Definition 2.6.1 — quantum posets
      KLM (2024) §3.1            — quantum preorders, convergence
      Weaver (2010) Definition 2.4 — quantum partial orders
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order.


(* ================================================================== *)
(*  §1  Descending ω-chains                                           *)
(* ================================================================== *)
(*
    A descending ω-chain in a preorder P is a monotone-decreasing
    sequence d : nat → P satisfying m ≤ n → d(n) ⊑ d(m).

    This is the order-dual of [chain] from Order.v.  It is needed for
    the convergence condition in quantum CPOs (KLM Definition 3.1.1):

      Kₙ ↗ K∞  iff  R ∘ K∞ = ⋀ₙ R ∘ Kₙ

    where the right-hand side is an infimum of a descending sequence
    in the quantale Q.
*)

Record desc_chain (P : Preorder.type) : Type := Build_desc_chain {
    dch : nat -> P;
    dch_anti : forall (m n : nat), m <= n -> dch n ⊑ dch m;
}.

Arguments Build_desc_chain {P} dch dch_anti.
Arguments dch {P} d n.
Arguments dch_anti {P} d m n _.

Notation "d .[^ n ]" := (dch d n) (at level 9, format "d .[^ n ]").

Lemma desc_chain_succ_le {P : Preorder.type} (d : desc_chain P) (n : nat) :
    d.[^S n] ⊑ d.[^n].
Proof.
    apply dch_anti.
    apply le_S.
    apply le_n.
Qed.


(* ================================================================== *)
(*  §2  Quantale operations                                           *)
(* ================================================================== *)
(*
    An involutive quantale Q, in our formalization, is a partial order
    equipped with six operations:

      - q_top  : greatest element (unit for q_prod)
      - q_bot  : least element (used in the Kronecker delta)
      - q_prod : non-commutative tensor product
      - q_adj  : involution (adjoint / dagger)
      - q_meet : binary meet (greatest lower bound of two elements)
      - q_inf  : infimum of descending ω-chains

    Mathematically, a full involutive quantale is a complete lattice
    with q_prod distributing over arbitrary joins and q_adj reversing
    q_prod.  We axiomatize only the fragment needed for quantum CPO
    theory.

    references:
        https://ncatlab.org/nlab/show/quantale
        https://en.wikipedia.org/wiki/Quantale

    All operations are in one [HasQuantaleOps] mixin.  The axioms
    are separated into [IsInvQuantale] below, following the pattern
    of [HasSup] / [IsCPO] in CPO.v.
*)

HB.mixin Record HasQuantaleOps T of PartialOrder T := {
    q_top  : T;
    q_bot  : T;
    q_prod : T -> T -> T;
    q_adj  : T -> T;
    q_meet : T -> T -> T;
    q_inf  : desc_chain T -> T;
}.

HB.structure Definition QuantaleOps :=
    {T of PartialOrder T & HasQuantaleOps T}.


(* ================================================================== *)
(*  §3  Involutive quantale axioms                                     *)
(* ================================================================== *)
(*
    The axioms are organized in five groups:

    (a) Top / Bottom:  q_top is greatest, q_bot is least.
    (b) Product:       associative, q_top is two-sided unit,
                       monotone in the first argument.
    (c) Adjoint:       involutive, antitone.
    (d) Meet:          commutative binary greatest lower bound.
    (e) Infimum:       greatest lower bound of descending ω-chains.

    These 14 axioms capture the fragment of involutive-quantale
    theory needed for quantum CPOs.  The consistency of this axiom
    set is justified by the concrete model B(H) — bounded operators
    on a Hilbert space.
*)

HB.mixin Record IsInvQuantale T of PartialOrder T & HasQuantaleOps T := {
    (* -- (a) Top / Bottom ----------------------------------------- *)
    q_top_greatest : forall (a : T), a ⊑ q_top;
    q_bot_least    : forall (a : T), q_bot ⊑ a;

    (* -- (b) Product ---------------------------------------------- *)
    q_prod_assoc  : forall (a b c : T),
        q_prod (q_prod a b) c = q_prod a (q_prod b c);
    q_prod_top_l  : forall (a : T), q_prod q_top a = a;
    q_prod_top_r  : forall (a : T), q_prod a q_top = a;
    q_prod_mono_l : forall (a b c : T),
        a ⊑ b -> q_prod a c ⊑ q_prod b c;
    q_prod_mono_r : forall (a b c : T),
        a ⊑ b -> q_prod c a ⊑ q_prod c b;

    (* -- (c) Adjoint ---------------------------------------------- *)
    q_adj_involutive : forall (a : T), q_adj (q_adj a) = a;
    q_adj_antitone   : forall (a b : T), a ⊑ b -> q_adj b ⊑ q_adj a;

    (* -- (d) Meet ------------------------------------------------- *)
    q_meet_comm     : forall (a b : T), q_meet a b = q_meet b a;
    q_meet_lower_l  : forall (a b : T), q_meet a b ⊑ a;
    q_meet_lower_r  : forall (a b : T), q_meet a b ⊑ b;
    q_meet_greatest : forall (a b c : T),
        c ⊑ a -> c ⊑ b -> c ⊑ q_meet a b;

    (* -- (e) Descending-chain infimum ----------------------------- *)
    q_inf_lower    : forall (d : desc_chain T) (n : nat),
        q_inf d ⊑ d.[^n];
    q_inf_greatest : forall (d : desc_chain T) (x : T),
        (forall (n : nat), x ⊑ d.[^n]) -> x ⊑ q_inf d;
}.

HB.structure Definition InvQuantale :=
    {T of PartialOrder T & HasQuantaleOps T & IsInvQuantale T}.

Notation "InvQuantale.type" := InvQuantale.type (only parsing).


(* ================================================================== *)
(*  §4  Notation                                                       *)
(* ================================================================== *)

Notation "a ⊗ b" := (q_prod a b) (at level 40, left associativity).
Notation "a ⊓ b" := (q_meet a b) (at level 45, left associativity).


(* ================================================================== *)
(*  §5  Kronecker delta                                                *)
(* ================================================================== *)
(*
    The Kronecker delta δ_Q(x, y) is the Q-valued identity relation:

      δ_Q(x, y) = q_top  if x = y
                 = q_bot  if x ≠ y

    This is the atom-level representation of the identity relation I_X
    in KLM's formalism.  It appears in the antisymmetry axiom:

      R ∧ R† ≤ I_X   translates to:
      (qord x y) ⊓ (qord y x)† ⊑ q_delta x y

    Requires decidable equality on X.
*)

Definition q_delta {Q : InvQuantale.type} {X : Type}
    (dec : forall (x y : X), {x = y} + {x <> y})
    (x y : X) : Q :=
    if dec x y then q_top else q_bot.

Lemma q_delta_refl {Q : InvQuantale.type} {X : Type}
    (dec : forall (x y : X), {x = y} + {x <> y}) (x : X) :
    q_delta dec x x = (q_top : Q).
Proof.
    unfold q_delta.
    destruct (dec x x) as [_ | Hneq].
    - reflexivity.
    - exfalso. apply Hneq. reflexivity.
Qed.

Lemma q_delta_neq {Q : InvQuantale.type} {X : Type}
    (dec : forall (x y : X), {x = y} + {x <> y}) (x y : X) :
    x <> y -> q_delta dec x y = (q_bot : Q).
Proof.
    intro Hneq.
    unfold q_delta.
    destruct (dec x y) as [Heq | _].
    - exfalso. apply Hneq. exact Heq.
    - reflexivity.
Qed.


(* ================================================================== *)
(*  §6  Quantum posets                                                 *)
(* ================================================================== *)
(*
    A quantum poset (X, R) consists of a type X (the "atom type")
    equipped with a Q-valued relation R : X → X → Q satisfying:

    - Reflexivity:    I_X ≤ R       i.e., q_top ⊑ R(x, x)
    - Transitivity:   R ∘ R ≤ R    i.e., R(x,y) ⊗ R(y,z) ⊑ R(x,z)
    - Antisymmetry:   R ∧ R† ≤ I_X i.e., R(x,y) ⊓ R(y,x)† ⊑ δ(x,y)

    Decidable equality on X is required for the Kronecker delta in
    the antisymmetry condition.

    The [qposet] record is parametrized by Q : InvQuantale.type,
    following the same design pattern as [chain] and [mono_fun] in
    Order.v: it is data built on an existing structure, not a new
    HB carrier.

    KLM Definition 2.6.1.
    Weaver (2010) Definition 2.4.
*)

Record qposet (Q : InvQuantale.type) : Type := Build_qposet {
    qp_carrier :> Type;
    qp_ord     : qp_carrier -> qp_carrier -> Q;
    qp_dec_eq  : forall (x y : qp_carrier), {x = y} + {x <> y};
    qp_refl    : forall (x : qp_carrier),
        q_top ⊑ qp_ord x x;
    qp_trans   : forall (x y z : qp_carrier),
        qp_ord x y ⊗ qp_ord y z ⊑ qp_ord x z;
    qp_antisym : forall (x y : qp_carrier),
        qp_ord x y ⊓ q_adj (qp_ord y x) ⊑ q_delta qp_dec_eq x y;
}.

Arguments Build_qposet {Q} qp_carrier qp_ord qp_dec_eq
    qp_refl qp_trans qp_antisym.
Arguments qp_carrier {Q} X : rename.
Arguments qp_ord {Q} X x y : rename.
Arguments qp_dec_eq {Q} X x y : rename.
Arguments qp_refl {Q} X x : rename.
Arguments qp_trans {Q} X x y z : rename.
Arguments qp_antisym {Q} X x y : rename.


(* ================================================================== *)
(*  §7  Derived properties                                             *)
(* ================================================================== *)
(*
    Properties derived from the quantale and quantum-poset axioms.
    These are used as building blocks in downstream files (qCPO.v).
*)

Section QPosetProperties.

Context {Q : InvQuantale.type} {X : qposet Q}.

(** Left antitonicity of qp_ord:

    If x ⊑ y in the quantum order (i.e., q_top ⊑ qp_ord x y),
    then qp_ord(y, z) ⊑ qp_ord(x, z) for all z.

    This is the main property needed by qCPO.v to show that
    ascending quantum chains produce descending sequences in Q.

    Derivation:
      qp_ord(y, z) = q_top ⊗ qp_ord(y, z)      (left unit)
                    ⊑ qp_ord(x, y) ⊗ qp_ord(y, z)  (mono_l + hypothesis)
                    ⊑ qp_ord(x, z)                    (transitivity)
*)
Lemma qp_antitone_l (x y z : X) :
    q_top ⊑ qp_ord X x y -> qp_ord X y z ⊑ qp_ord X x z.
Proof.
    intro Hxy.
    assert (Hstep : q_top ⊗ qp_ord X y z ⊑ qp_ord X x y ⊗ qp_ord X y z).
    { apply q_prod_mono_l. exact Hxy. }
    assert (Heq : (q_top : Q) ⊗ qp_ord X y z = qp_ord X y z).
    { exact (q_prod_top_l _). }
    rewrite Heq in Hstep.
    apply @le_trans with (y := qp_ord X x y ⊗ qp_ord X y z).
    - exact Hstep.
    - apply qp_trans.
Qed.

(** Right covariance of qp_ord:

    If y ⊑ z in the quantum order (i.e., q_top ⊑ qp_ord y z),
    then qp_ord(x, y) ⊑ qp_ord(x, z) for all x.

    Derivation:
      qp_ord(x, y) = qp_ord(x, y) ⊗ q_top      (right unit)
                    ⊑ qp_ord(x, y) ⊗ qp_ord(y, z)  (mono_r + hypothesis)
                    ⊑ qp_ord(x, z)                    (transitivity)
*)
Lemma qp_covariant_r (x y z : X) :
    q_top ⊑ qp_ord X y z -> qp_ord X x y ⊑ qp_ord X x z.
Proof.
    intro Hyz.
    assert (Hstep : qp_ord X x y ⊗ q_top ⊑ qp_ord X x y ⊗ qp_ord X y z).
    { apply q_prod_mono_r. exact Hyz. }
    assert (Heq : qp_ord X x y ⊗ (q_top : Q) = qp_ord X x y).
    { exact (q_prod_top_r _). }
    rewrite Heq in Hstep.
    apply @le_trans with (y := qp_ord X x y ⊗ qp_ord X y z).
    - exact Hstep.
    - apply qp_trans.
Qed.

End QPosetProperties.
