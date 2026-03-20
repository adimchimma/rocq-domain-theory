(*  qCPO — Quantum Complete Partial Orders

    Phase 2: Quantum chains, convergence, and quantum CPOs following
    Kornell, Lindenhovius & Mislove (2024), §3.

    This is [src/quantum/qCPO.v].  It consumes the structures from
    QuantumStructure.v (InvQuantale, qposet, desc_chain) and builds
    the theory of quantum chains, convergence, and quantum CPOs.

    Contents:
      §1  Quantum chains          — ascending sequences K : nat → (W → X)
      §2  Descending order chains — qord ∘ K is descending when K ascends
      §3  Convergence             — Kₙ ↗ K∞ iff R ∘ K∞ = ⋀ₙ R ∘ Kₙ
      §4  Convergence properties  — upper bound, uniqueness, equivalences
      §5  Quantum CPO             — every quantum chain has a limit
      §6  Constant chains         — trivial chain converges to itself
      §7  Quantum monotonicity    — F preserves quantum order
      §8  Mapping chains          — monotone F applied to a chain
      §9  Scott continuity        — F preserves convergence
      §10 Pointed quantum CPOs    — bottom element

    Design decision (DD-022):
      Quantum chains and convergence are parametrized by an arbitrary
      quantum poset (X : qposet Q) and an arbitrary "probe" type
      (W : Type).  This avoids the duplication seen in earlier drafts
      where qchain/converges/descending-chain were duplicated for X
      and Y.  Scott continuity is then stated as: monotone F maps
      X-chains to Y-chains and preserves convergence.

    Imports:
      QuantumStructure.v — InvQuantale, qposet, desc_chain,
                           qp_ord, qp_antitone_l, q_inf, etc.

    References:
      KLM §3.1, Definition 3.1.1 — convergence (Kₙ ↗ K∞)
      KLM §3.2, Definition 3.2.1 — quantum CPO
      KLM §3.2, Definition 3.2.4 — Scott continuity
      KLM §3.1, Proposition 3.1.5 — limit uniqueness
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order.
From DomainTheory.Quantum Require Import QuantumStructure.


(* ================================================================== *)
(*  §1  Quantum chains                                                 *)
(* ================================================================== *)
(*
    A quantum chain in a quantum poset (X, R) indexed by W is a
    sequence K : nat → (W → X) that is ascending in the quantum order:

      ∀ n w,  q_top ⊑ R(K(n, w), K(n+1, w))

    This is the atom-level representation of KLM's ascending sequence
    in qSet(W, X) with the pointwise order.

    KLM Definition 3.2.1 requires this only for atomic W; Proposition
    3.2.3 lifts to arbitrary W.  We state the general form.
*)

Section QuantumChains.

Context {Q : InvQuantale.type} {X : qposet Q} {W : Type}.

Definition qchain_ascending (K : nat -> W -> X) : Prop :=
    forall (n : nat) (w : W),
        (q_top : Q) ⊑ qp_ord X (K n w) (K (S n) w).

Record qchain : Type := Build_qchain {
    qch : nat -> W -> X;
    qch_ascending : qchain_ascending qch;
}.

Notation "K .[# n ]" := (qch K n) (at level 9, format "K .[# n ]").


(* ================================================================== *)
(*  §2  Descending order chains                                        *)
(* ================================================================== *)
(*
    When K is ascending, the sequence n ↦ R(K(n, w), x) is descending
    in Q for each fixed w and x.  This is because R is antitone in
    its first argument (qp_antitone_l from QuantumStructure.v §7):

      K(n) ⊑ K(n+1)  ⟹  R(K(n+1), x) ⊑ R(K(n), x)

    We package this as a desc_chain in Q, which is the data structure
    needed for q_inf.
*)

Lemma qord_chain_descending (K : qchain) (w : W) (x : X) :
    forall (m n : nat), m <= n ->
        qp_ord X (qch K n w) x ⊑ qp_ord X (qch K m w) x.
Proof.
    intros m n Hmn.
    induction Hmn as [| n' Hmn' IH].
    - apply (@le_refl Q).
    - apply @le_trans with (y := qp_ord X (qch K n' w) x).
      + apply qp_antitone_l.
        apply qch_ascending.
      + exact IH.
Qed.

Definition qord_desc_chain (K : qchain) (w : W) (x : X)
    : desc_chain Q :=
    Build_desc_chain
        (fun n => qp_ord X (qch K n w) x)
        (qord_chain_descending K w x).


(* ================================================================== *)
(*  §3  Convergence                                                    *)
(* ================================================================== *)
(*
    KLM Definition 3.1.1:

    Given K₁ ⊑ K₂ ⊑ ... : W → X ascending in (X, R), a function
    K∞ : W → X is the limit (written Kₙ ↗ K∞) if:

        R ∘ K∞ = ⋀ₙ R ∘ Kₙ

    Pointwise: ∀ w x,  R(K∞(w), x) = inf_n R(K(n, w), x)

    Since Q is a partial order, we can split the equality into two
    directions (converges) or state it as a single equality
    (converges_eq).
*)

Definition converges (K : qchain) (K_inf : W -> X) : Prop :=
    forall (w : W) (x : X),
        qp_ord X (K_inf w) x ⊑ q_inf (qord_desc_chain K w x)
        /\
        q_inf (qord_desc_chain K w x) ⊑ qp_ord X (K_inf w) x.

Definition converges_eq (K : qchain) (K_inf : W -> X) : Prop :=
    forall (w : W) (x : X),
        qp_ord X (K_inf w) x = q_inf (qord_desc_chain K w x).


(* ================================================================== *)
(*  §4  Convergence properties                                         *)
(* ================================================================== *)

Lemma converges_iff_eq (K : qchain) (K_inf : W -> X) :
    converges K K_inf <-> converges_eq K K_inf.
Proof.
    split.
    - intros Hconv w x.
      apply (@le_antisym Q).
      + exact (proj1 (Hconv w x)).
      + exact (proj2 (Hconv w x)).
    - intros Heq w x.
      rewrite (Heq w x).
      split; apply (@le_refl Q).
Qed.

(* 
    The limit is an upper bound: if Kₙ ↗ K∞ then for each n,
    K(n, w) ⊑ K∞(w) in the quantum order.

    More precisely: qord(K∞ w, K∞ w) ⊑ qord(K n w, K∞ w),
    so by reflexivity (q_top ⊑ qord(K∞ w, K∞ w)) we get
    q_top ⊑ qord(K n w, K∞ w). 
*)
Lemma converges_upper (K : qchain) (K_inf : W -> X) :
    converges K K_inf ->
    forall (n : nat) (w : W),
        qp_ord X (K_inf w) (K_inf w) ⊑ qp_ord X (qch K n w) (K_inf w).
Proof.
    intros Hconv n w.
    destruct (Hconv w (K_inf w)) as [Hle _].
    apply @le_trans with (y := q_inf (qord_desc_chain K w (K_inf w))).
    - exact Hle.
    - exact (q_inf_lower (qord_desc_chain K w (K_inf w)) n).
Qed.

Lemma converges_upper_top (K : qchain) (K_inf : W -> X) :
    converges K K_inf ->
    forall (n : nat) (w : W),
        (q_top : Q) ⊑ qp_ord X (qch K n w) (K_inf w).
Proof.
    intros Hconv n w.
    apply @le_trans with (y := qp_ord X (K_inf w) (K_inf w)).
    - apply qp_refl.
    - apply converges_upper. exact Hconv.
Qed.

(*  
    Limit uniqueness: if Kₙ ↗ K∞ and Kₙ ↗ K∞', then
    qord(K∞ w, x) = qord(K∞' w, x) for all w, x.

    KLM Proposition 3.1.5. 
*)
Lemma converges_unique (K : qchain) (K_inf K_inf' : W -> X) :
    converges K K_inf -> converges K K_inf' ->
    forall (w : W) (x : X),
        qp_ord X (K_inf w) x = qp_ord X (K_inf' w) x.
Proof.
    intros Hconv Hconv' w x.
    apply (@le_antisym Q).
    - apply @le_trans with (y := q_inf (qord_desc_chain K w x)).
      + exact (proj1 (Hconv w x)).
      + exact (proj2 (Hconv' w x)).
    - apply @le_trans with (y := q_inf (qord_desc_chain K w x)).
      + exact (proj1 (Hconv' w x)).
      + exact (proj2 (Hconv w x)).
Qed.


(* ================================================================== *)
(*  §5  Quantum CPO                                                    *)
(* ================================================================== *)
(*
    KLM Definition 3.2.1:

    A quantum poset (X, R) is a quantum CPO if, for each quantum
    set W, every ascending sequence K : W → X has a limit K∞.

    We provide both a propositional version (is_qcpo) and a
    data-carrying version (QCPOData) with a definite limit operation.
*)

Definition is_qcpo : Prop :=
    forall (K : qchain), exists (K_inf : W -> X), converges K K_inf.

Record QCPOData : Type := Build_QCPOData {
    qlimit : qchain -> (W -> X);
    qlimit_converges : forall (K : qchain), converges K (qlimit K);
}.


(* ================================================================== *)
(*  §6  Constant chains                                                *)
(* ================================================================== *)
(*
    The constant sequence K(n) = f for all n is trivially ascending
    and converges to f.  This is useful for showing that identity
    is Scott-continuous (qCPOProperties.v).
*)

Lemma qchain_const_ascending (f : W -> X) :
    qchain_ascending (fun _ => f).
Proof.
    intros n w.
    apply qp_refl.
Qed.

Definition qchain_const (f : W -> X) : qchain :=
    Build_qchain (fun _ => f) (qchain_const_ascending f).

Lemma converges_const (f : W -> X) :
    converges (qchain_const f) f.
Proof.
    intros w x. split.
    - apply (q_inf_greatest (qord_desc_chain (qchain_const f) w x)).
      intro n. apply (@le_refl Q).
    - exact (q_inf_lower (qord_desc_chain (qchain_const f) w x) 0).
Qed.

End QuantumChains.

Arguments Build_qchain {Q X W} qch qch_ascending : assert.
Arguments qch {Q X W} K n w : rename.
Arguments qch_ascending {Q X W} K n w : rename.
Arguments qord_desc_chain {Q X W} K w x : rename.
Arguments converges {Q X W} K K_inf : rename.
Arguments converges_eq {Q X W} K K_inf : rename.
Arguments is_qcpo {Q} X W : rename.
Arguments Build_QCPOData {Q X W} qlimit qlimit_converges : assert.
Arguments qlimit {Q X W} D K : rename.
Arguments qlimit_converges {Q X W} D K : rename.
Arguments qchain_const {Q X W} f : rename.


(* ================================================================== *)
(*  §7  Quantum monotonicity                                           *)
(* ================================================================== *)
(*
    A function F : X → Y between quantum posets is monotone if
    it preserves the quantum order:

      ∀ x x',  R_X(x, x') ⊑ R_Y(F x, F x')

    This is the atom-level reading of the condition S ∘ F ≥ F ∘ R
    from KLM.
*)

Section QMonotone.

Context {Q : InvQuantale.type} {X Y : qposet Q}.

Definition q_monotone (F : X -> Y) : Prop :=
    forall (x x' : X),
        qp_ord X x x' ⊑ qp_ord Y (F x) (F x').


(* ================================================================== *)
(*  §8  Mapping chains                                                 *)
(* ================================================================== *)
(*
    A monotone function F : X → Y maps ascending X-chains to
    ascending Y-chains.  This is because:

      q_top ⊑ R_X(K n w, K (S n) w)
            ⊑ R_Y(F(K n w), F(K (S n) w))

    We then package this as a qchain in Y.
*)

Lemma q_monotone_preserves_ascending {W : Type}
    (F : X -> Y) (HF : q_monotone F) (K : @qchain Q X W) :
    @qchain_ascending Q Y W (fun n w => F (qch K n w)).
Proof.
    intros n w.
    apply @le_trans with (y := qp_ord X (qch K n w) (qch K (S n) w)).
    - apply qch_ascending.
    - apply HF.
Qed.

Definition map_qchain {W : Type}
    (F : X -> Y) (HF : q_monotone F) (K : @qchain Q X W)
    : @qchain Q Y W :=
    Build_qchain
        (fun n w => F (qch K n w))
        (q_monotone_preserves_ascending F HF K).


(* ================================================================== *)
(*  §9  Scott continuity                                               *)
(* ================================================================== *)
(*
    KLM Definition 3.2.4:

    A monotone function F : (X, R) → (Y, S) is Scott continuous if
    it preserves convergence of quantum chains:

      Kₙ ↗ K∞  ⟹  F ∘ Kₙ ↗ F ∘ K∞

    Stated using the convergence relation from §3.
*)

Definition q_scott_continuous (F : X -> Y) : Prop :=
    exists (HF : q_monotone F),
    forall (W : Type) (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        converges (map_qchain F HF K) (fun w => F (K_inf w)).

End QMonotone.

Arguments q_monotone {Q X Y} F : rename.
Arguments map_qchain {Q X Y W} F HF K : rename.
Arguments q_scott_continuous {Q X Y} F : rename.


(* ================================================================== *)
(*  §10 Pointed quantum CPOs                                           *)
(* ================================================================== *)
(*
    A pointed quantum CPO has a bottom element ⊥ such that
    q_top ⊑ R(⊥, x) for all x — i.e., ⊥ is below everything
    in the quantum order.

    This will be needed for the lift monad (KLM §7).
*)

Section PointedQCPO.

Context {Q : InvQuantale.type} {X : qposet Q}.

Definition is_q_bottom (bot : X) : Prop :=
    forall (x : X), (q_top : Q) ⊑ qp_ord X bot x.

Record QBottom : Type := Build_QBottom {
    q_bot_elem : X;
    q_bot_proof : is_q_bottom q_bot_elem;
}.

Definition is_pointed_qcpo (W : Type) : Prop :=
    is_qcpo X W /\ exists (bot : X), is_q_bottom bot.

End PointedQCPO.

Arguments is_q_bottom {Q X} bot : rename.
Arguments Build_QBottom {Q X} q_bot_elem q_bot_proof : assert.
Arguments q_bot_elem {Q X} B : rename.
Arguments q_bot_proof {Q X} B : rename.
Arguments is_pointed_qcpo {Q} X W : rename.
