(*  qCPOProperties — Properties of Quantum CPOs

    Phase 2: Category-theoretic properties of quantum CPOs, bundled
    continuous maps, fixed points, and CPO-enrichment of hom-sets.

    This is [src/quantum/qCPOProperties.v].  It builds on
    QuantumStructure.v and qCPO.v to develop the
    category-theoretic infrastructure for quantum domain theory.

    Contents:
      §1   Bundled continuous maps   — [q_cont_fun] record (split fields)
      §2   Identity is continuous    — [q_cont_id]
      §3   Constant map is continuous— [q_cont_const]
      §4   Composition of chains     — [map_qchain_comp]
      §5   Composition is continuous — [q_cont_comp]
      §6   Category laws             — assoc, id_l, id_r, extensionality
      §7   Bottom uniqueness         — quantum bottoms are equal in order
      §8   Cofinal subsequences      — reindexing preserves convergence
      §9   Pointwise quantum order   — ordering on hom-sets
      §10  CPO-enrichment            — chain of continuous funs converges
      §11  Kleene fixed point        — iteration, fixp, Scott induction

    Design decision (DD-023):
      [q_cont_fun] splits monotonicity and convergence-preservation into
      two separate record fields, rather than embedding monotonicity
      inside an existential as in [q_scott_continuous].  This avoids
      proof-witness mismatch when composing [map_qchain] applications.
      A bridge lemma [q_cont_fun_scott_continuous] establishes equivalence
      with the existential formulation in qCPO.v.

    Imports:
      QuantumStructure.v — InvQuantale, qposet, desc_chain, q_delta, etc.
      qCPO.v             — qchain, converges, q_monotone, map_qchain,
                           q_scott_continuous, QCPOData, QBottom, etc.

    References:
      KLM §3.2, Proposition 3.2.6  — continuous composition
      KLM §3.2, Remark 3.2.7       — constant functions are continuous
      KLM §3.2, Definition 3.2.9   — category qCPO
      KLM §3.3, Theorem 3.3.5      — CPO-enrichment of hom-sets
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO.
From DomainTheory.Quantum Require Import QuantumStructure qCPO.

From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PeanoNat.


(* ================================================================== *)
(*  §0  Auxiliary: convergence transfer for pointwise-equal chains     *)
(* ================================================================== *)
(*
    Two qchains with the same underlying sequence (but possibly
    different ascending-proof witnesses) have the same desc_chains
    and hence the same convergence behavior.

    This is needed repeatedly: map_qchain id K vs K,
    map_qchain G (map_qchain F K) vs map_qchain (G∘F) K, etc.
*)

Section ConvergenceTransfer.

Context {Q : InvQuantale.type} {X : qposet Q} {W : Type}.

Lemma converges_ext (K1 K2 : @qchain Q X W) (K_inf : W -> X) :
    (forall n w, qch K1 n w = qch K2 n w) ->
    converges K1 K_inf -> converges K2 K_inf.
Proof.
    intros Heq Hconv w x.
    split.
    - apply @le_trans with (y := q_inf (qord_desc_chain K1 w x)).
      + exact (proj1 (Hconv w x)).
      + apply q_inf_greatest. intro n.
        apply @le_trans with (y := dch (qord_desc_chain K1 w x) n).
        * apply q_inf_lower.
        * simpl. rewrite (Heq n w). apply (@le_refl Q).
    - apply @le_trans with (y := q_inf (qord_desc_chain K1 w x)).
      + apply q_inf_greatest. intro n.
        apply @le_trans with (y := dch (qord_desc_chain K2 w x) n).
        * apply q_inf_lower.
        * simpl. rewrite (Heq n w). apply (@le_refl Q).
      + exact (proj2 (Hconv w x)).
Qed.

End ConvergenceTransfer.


(* ================================================================== *)
(*  §1  Bundled continuous maps                                        *)
(* ================================================================== *)
(*
    A quantum Scott-continuous map between quantum posets X and Y
    (over the same involutive quantale Q) packages:
      (1) the underlying function F : X → Y
      (2) a proof that F is monotone (preserves quantum order)
      (3) a proof that F preserves convergence for all probe types W

    This is the quantum analogue of [cont_fun] from Morphisms.v.

    The split-field design (monotonicity + convergence-preservation
    as separate fields rather than monotonicity inside an existential)
    means we always have direct access to the monotonicity witness,
    which is needed as an argument to [map_qchain].
*)

Section QContFun.

Context {Q : InvQuantale.type}.

Record q_cont_fun (X Y : qposet Q) : Type := Build_q_cont_fun {
    qcf_fun :> X -> Y;
    qcf_mono : q_monotone qcf_fun;
    qcf_preserves : forall (W : Type) (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        converges (map_qchain qcf_fun qcf_mono K) (fun w => qcf_fun (K_inf w));
}.

Arguments Build_q_cont_fun {X Y} qcf_fun qcf_mono qcf_preserves.
Arguments qcf_fun {X Y} f x : rename.
Arguments qcf_mono {X Y} f x x' : rename.
Arguments qcf_preserves {X Y} f W K K_inf _ : rename.

Notation "[ X →qc Y ]" := (q_cont_fun X Y)
    (at level 0, Y at level 200, no associativity).

(*  Bridge to the existential formulation in qCPO.v. *)
Lemma q_cont_fun_scott_continuous {X Y : qposet Q} (f : [X →qc Y]) :
    q_scott_continuous (qcf_fun f).
Proof.
    exists (qcf_mono f).
    intros W K K_inf Hconv.
    exact (qcf_preserves f W K K_inf Hconv).
Qed.


(* ================================================================== *)
(*  §2  Identity is continuous                                         *)
(* ================================================================== *)
(*
    The identity function id : X → X is trivially monotone (the quantum
    order is preserved by doing nothing) and preserves convergence
    (map_qchain id K has the same underlying sequence as K).

    For convergence-preservation, the key is that
      qp_ord Y (id (K n w)) x = qp_ord X (K n w) x
    so the infima are the same, and the convergence proof carries over.

    Uses [qchain_const] and [converges_const] from qCPO.v §6.
*)

Lemma q_monotone_id (X : qposet Q) : q_monotone (fun x : X => x).
Proof.
    intros x x'.
    apply (@le_refl Q).
Qed.

Lemma q_id_preserves (X : qposet Q) :
    forall (W : Type) (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        converges (map_qchain (fun x : X => x) (q_monotone_id X) K)
                  (fun w => K_inf w).
Proof.
    intros W K K_inf Hconv w x.
    (* The mapped chain has the same underlying sequence as K,
       so the desc_chains agree pointwise at every index. *)
    assert (Hdeq : forall n,
        dch (qord_desc_chain (map_qchain (fun x0 : X => x0) (q_monotone_id X) K) w x) n =
        dch (qord_desc_chain K w x) n).
    { intro n. reflexivity. }
    split.
    - apply @le_trans with (y := q_inf (qord_desc_chain K w x)).
      + exact (proj1 (Hconv w x)).
      + apply q_inf_greatest.
        intro n.
        apply @le_trans with (y := dch (qord_desc_chain K w x) n).
        * apply q_inf_lower.
        * rewrite <- (Hdeq n). apply (@le_refl Q).
    - apply @le_trans with (y := q_inf (qord_desc_chain K w x)).
      + apply q_inf_greatest.
        intro n.
        apply @le_trans with
            (y := dch (qord_desc_chain
                (map_qchain (fun x0 : X => x0) (q_monotone_id X) K) w x) n).
        * apply q_inf_lower.
        * rewrite (Hdeq n). apply (@le_refl Q).
      + exact (proj2 (Hconv w x)).
Qed.

Definition q_cont_id (X : qposet Q) : [X →qc X] :=
    Build_q_cont_fun
        (fun x => x)
        (q_monotone_id X)
        (q_id_preserves X).


(* ================================================================== *)
(*  §3  Constant function is continuous                                *)
(* ================================================================== *)
(*
    For any c : Y, the constant function (fun _ => c) : X → Y is
    Scott-continuous.  KLM Remark 3.2.7.

    Monotonicity: qp_ord Y c c ≥ q_top ≥ ... is trivially monotone
    since the output doesn't depend on the input.

    Convergence: the image chain is constant at c, so it converges
    to c by [converges_const] from qCPO.v.
*)

Lemma q_monotone_const {X Y : qposet Q} (c : Y) :
    q_monotone (fun _ : X => c).
Proof.
    intros x x'.
    apply @le_trans with (y := (q_top : Q)).
    - apply q_top_greatest.
    - apply qp_refl.
Qed.

Lemma q_const_preserves {X Y : qposet Q} (c : Y) :
    forall (W : Type) (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        converges (map_qchain (fun _ : X => c) (q_monotone_const c) K)
                  (fun _ => c).
Proof.
    intros W K K_inf _Hconv.
    apply converges_ext with
        (K1 := qchain_const (fun _ : W => c)).
    - intros n w. reflexivity.
    - apply converges_const.
Qed.

Definition q_cont_const {X Y : qposet Q} (c : Y) : [X →qc Y] :=
    Build_q_cont_fun
        (fun _ => c)
        (q_monotone_const c)
        (q_const_preserves c).


(* ================================================================== *)
(*  §4  Composition of mapped chains                                   *)
(* ================================================================== *)
(*
    For monotone F : X → Y and G : Y → Z, mapping a chain K first by F
    then by G produces a chain whose underlying sequence is the same as
    mapping by (G ∘ F) directly.  The proof witnesses for qch_ascending
    differ, but the underlying nat → W → Z functions agree pointwise.

    This is needed for the composition-preserves-convergence proof in §5.
*)

Section MapQchainComp.

Context {X Y Z : qposet Q}.

Lemma q_monotone_comp (G : Y -> Z) (F : X -> Y) :
    q_monotone G -> q_monotone F -> q_monotone (fun x => G (F x)).
Proof.
    intros HG HF x x'.
    apply @le_trans with (y := qp_ord Y (F x) (F x')).
    - apply HF.
    - apply HG.
Qed.

(*
    The underlying sequences of [map_qchain G HG (map_qchain F HF K)]
    and [map_qchain (G ∘ F) Hcomp K] agree pointwise.
*)
Lemma map_qchain_comp_eq {W : Type}
    (G : Y -> Z) (HG : q_monotone G)
    (F : X -> Y) (HF : q_monotone F)
    (K : @qchain Q X W) :
    forall (n : nat) (w : W),
        qch (map_qchain G HG (map_qchain F HF K)) n w =
        qch (map_qchain (fun x => G (F x)) (q_monotone_comp G F HG HF) K) n w.
Proof.
    intros n w.
    reflexivity.
Qed.

End MapQchainComp.


(* ================================================================== *)
(*  §5  Composition of continuous maps                                 *)
(* ================================================================== *)
(*
    KLM Proposition 3.2.6 (part):

    If F : X → Y and G : Y → Z are Scott-continuous, then
    G ∘ F : X → Z is Scott-continuous.

    Proof: monotonicity composes (§4).  For convergence, if Kₙ ↗ K∞
    then F(Kₙ) ↗ F(K∞) by continuity of F, then G(F(Kₙ)) ↗ G(F(K∞))
    by continuity of G.  The chain G(F(Kₙ)) is definitionally equal to
    map_qchain (G ∘ F) K.
*)

Section QContComp.

Context {X Y Z : qposet Q}.

Lemma q_comp_preserves
    (G : Y -> Z) (HG_mono : q_monotone G)
    (HG_pres : forall (W : Type) (K : @qchain Q Y W) (K_inf : W -> Y),
        converges K K_inf ->
        converges (map_qchain G HG_mono K) (fun w => G (K_inf w)))
    (F : X -> Y) (HF_mono : q_monotone F)
    (HF_pres : forall (W : Type) (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        converges (map_qchain F HF_mono K) (fun w => F (K_inf w))) :
    forall (W : Type) (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        converges (map_qchain (fun x => G (F x))
                              (q_monotone_comp G F HG_mono HF_mono) K)
                  (fun w => G (F (K_inf w))).
Proof.
    intros W K K_inf Hconv.
    (* F preserves convergence: F(Kₙ) ↗ F(K∞) *)
    specialize (HF_pres W K K_inf Hconv) as HFK.
    (* G preserves convergence: G(F(Kₙ)) ↗ G(F(K∞)) *)
    specialize (HG_pres W (map_qchain F HF_mono K) (fun w => F (K_inf w)) HFK) as HGFK.
    (* Transfer: map_qchain G (map_qchain F K) has the same
       underlying sequence as map_qchain (G ∘ F) K *)
    apply converges_ext with
        (K1 := map_qchain G HG_mono (map_qchain F HF_mono K)).
    - intros n w. reflexivity.
    - exact HGFK.
Qed.

Definition q_cont_comp (g : [Y →qc Z]) (f : [X →qc Y]) : [X →qc Z] :=
    Build_q_cont_fun
        (fun x => g (f x))
        (q_monotone_comp g f (qcf_mono g) (qcf_mono f))
        (q_comp_preserves g (qcf_mono g) (qcf_preserves g)
                          f (qcf_mono f) (qcf_preserves f)).

End QContComp.

Arguments q_cont_comp {X Y Z} g f : rename.

Notation "g ∘q f" := (q_cont_comp g f) (at level 40, left associativity).


(* ================================================================== *)
(*  §6  Category laws                                                  *)
(* ================================================================== *)
(*
    The quantum CPO morphisms form a category with [q_cont_id] as
    identity and [q_cont_comp] as composition, satisfying:
      - Left identity:  id ∘ f = f
      - Right identity: f ∘ id = f
      - Associativity:  h ∘ (g ∘ f) = (h ∘ g) ∘ f
      - Extensionality: equal underlying functions ⟹ equal q_cont_funs

    These follow the pattern of [cont_comp_id_l], [cont_comp_id_r],
    [cont_comp_assoc], [cont_fun_eq] from Morphisms.v.

    KLM Definition 3.2.9.
*)

Lemma q_cont_fun_eq {X Y : qposet Q} (f g : [X →qc Y]) :
    (forall x, qcf_fun f x = qcf_fun g x) -> f = g.
Proof.
    intro Hext.
    assert (Hfeq : qcf_fun f = qcf_fun g).
    { extensionality x. exact (Hext x). }
    destruct f as [f_fun f_mono f_pres].
    destruct g as [g_fun g_mono g_pres].
    simpl in Hfeq.
    subst g_fun.
    assert (Hmeq : f_mono = g_mono) by apply proof_irrelevance.
    subst g_mono.
    assert (Hpeq : f_pres = g_pres) by apply proof_irrelevance.
    subst g_pres.
    reflexivity.
Qed.

Lemma q_cont_comp_id_l {X Y : qposet Q} (f : [X →qc Y]) :
    q_cont_comp (q_cont_id Y) f = f.
Proof.
    apply q_cont_fun_eq.
    intro x. reflexivity.
Qed.

Lemma q_cont_comp_id_r {X Y : qposet Q} (f : [X →qc Y]) :
    q_cont_comp f (q_cont_id X) = f.
Proof.
    apply q_cont_fun_eq.
    intro x. reflexivity.
Qed.

Lemma q_cont_comp_assoc {X Y Z W : qposet Q}
    (h : [Z →qc W]) (g : [Y →qc Z]) (f : [X →qc Y]) :
    q_cont_comp h (q_cont_comp g f) = q_cont_comp (q_cont_comp h g) f.
Proof.
    apply q_cont_fun_eq.
    intro x. reflexivity.
Qed.


(* ================================================================== *)
(*  §7  Bottom uniqueness                                              *)
(* ================================================================== *)
(*
    In a quantum poset, if ⊥₁ and ⊥₂ are both quantum bottoms
    (i.e., q_top ⊑ R(⊥ᵢ, x) for all x), then they are equal in
    the quantum order:

      q_top ⊑ R(⊥₁, ⊥₂)  and  q_top ⊑ R(⊥₂, ⊥₁)

    In particular, their quantum orders to any third element agree:
      R(⊥₁, x) = R(⊥₂, x) for all x.
*)

Section BottomUniqueness.

Context {X : qposet Q}.

Lemma q_bottom_le (b1 b2 : X) :
    is_q_bottom b1 -> is_q_bottom b2 ->
    (q_top : Q) ⊑ qp_ord X b1 b2.
Proof.
    intros Hb1 _Hb2.
    exact (Hb1 b2).
Qed.

Lemma q_bottom_ord_eq (b1 b2 : X) (x : X) :
    is_q_bottom b1 -> is_q_bottom b2 ->
    qp_ord X b1 x = qp_ord X b2 x.
Proof.
    intros Hb1 Hb2.
    apply (@le_antisym Q).
    - (* R(b1, x) ⊑ R(b2, x) : antitone_l with q_top ⊑ R(b2, b1) *)
      apply qp_antitone_l.
      exact (Hb2 b1).
    - (* R(b2, x) ⊑ R(b1, x) : antitone_l with q_top ⊑ R(b1, b2) *)
      apply qp_antitone_l.
      exact (Hb1 b2).
Qed.

End BottomUniqueness.


(* ================================================================== *)
(*  §8  Cofinal subsequences                                          *)
(* ================================================================== *)
(*
    If φ : nat → nat is strictly increasing, then the subsequence
    K ∘ φ is still a quantum chain (ascending), and if K converges
    to K∞, so does K ∘ φ.

    This is used implicitly in KLM for reindexing arguments.
    The key insight: if K(n,w) ⊑ K(n+1,w) for all n, and φ is
    monotone, then K(φ(n),w) ⊑ K(φ(n+1),w) because
    φ(n) ≤ φ(n+1) and the chain is ascending.
*)

Section Cofinal.

Context {X : qposet Q} {W : Type}.

(*  A strictly increasing reindexing. *)
Definition strict_mono (φ : nat -> nat) : Prop :=
    forall n, φ n < φ (S n).

Lemma strict_mono_le (φ : nat -> nat) :
    strict_mono φ -> forall n, n <= φ n.
Proof.
    intros Hφ n.
    induction n.
    - apply Nat.le_0_l.
    - apply Nat.le_trans with (S (φ n)).
      + apply le_n_S. exact IHn.
      + exact (Hφ n).
Qed.

Lemma strict_mono_mono (φ : nat -> nat) :
    strict_mono φ -> forall m n, m <= n -> φ m <= φ n.
Proof.
    intros Hφ m n Hmn.
    induction Hmn.
    - apply le_n.
    - apply Nat.le_trans with (φ m0).
      + exact IHHmn.
      + apply Nat.lt_le_incl.
        exact (Hφ m0).
Qed.

Lemma cofinal_ascending (K : @qchain Q X W) (φ : nat -> nat)
    (Hφ : strict_mono φ) :
    @qchain_ascending Q X W (fun n w => qch K (φ n) w).
Proof.
    intros n w.
    (* q_top ⊑ R(K(φ(S n)), K(φ(S n)))  by reflexivity
       R(K(φ(S n)), K(φ(S n))) ⊑ R(K(φ n), K(φ(S n)))  by descending
       since φ n ≤ φ(S n) (from strict monotonicity). *)
    apply @le_trans with
        (y := qp_ord X (qch K (φ (S n)) w) (qch K (φ (S n)) w)).
    - apply qp_refl.
    - apply qord_chain_descending.
      apply Nat.lt_le_incl.
      exact (Hφ n).
Qed.

Definition cofinal_qchain (K : @qchain Q X W) (φ : nat -> nat)
    (Hφ : strict_mono φ) : @qchain Q X W :=
    Build_qchain
        (fun n w => qch K (φ n) w)
        (cofinal_ascending K φ Hφ).

(*
    If K converges to K∞, then K ∘ φ also converges to K∞.

    Proof: converges means R(K∞(w), x) = ⋀ₙ R(K(n,w), x).
    The subsequence ⋀ₙ R(K(φ(n),w), x) is a sub-infimum of the
    full infimum:
      - ⋀_full ⊑ ⋀_sub (fewer terms ⟹ larger inf)
      - ⋀_sub ⊑ ⋀_full (each K(φ(n)) term appears in the full chain,
        so ⋀_sub ⊑ R(K(φ(n),w), x) ⊑ R(K(n,w), x) by monotonicity,
        since n ≤ φ(n) and the desc_chain is antitone)
*)
Lemma cofinal_converges (K : @qchain Q X W) (K_inf : W -> X)
    (φ : nat -> nat) (Hφ : strict_mono φ) :
    converges K K_inf ->
    converges (cofinal_qchain K φ Hφ) K_inf.
Proof.
    intros Hconv w x. split.
    - (* R(K∞ w, x) ⊑ ⋀_n R(K(φ n, w), x) *)
      apply q_inf_greatest.
      intro n. simpl.
      apply @le_trans with (y := q_inf (qord_desc_chain K w x)).
      + exact (proj1 (Hconv w x)).
      + exact (q_inf_lower (qord_desc_chain K w x) (φ n)).
    - (* ⋀_n R(K(φ n, w), x) ⊑ R(K∞ w, x) *)
      apply @le_trans with (y := q_inf (qord_desc_chain K w x)).
      + apply q_inf_greatest.
        intro n.
        apply @le_trans with (y := qp_ord X (qch K (φ n) w) x).
        * simpl. exact (q_inf_lower
            (qord_desc_chain (cofinal_qchain K φ Hφ) w x) n).
        * apply qord_chain_descending.
          apply strict_mono_le.
          exact Hφ.
      + exact (proj2 (Hconv w x)).
Qed.

End Cofinal.


(* ================================================================== *)
(*  §9  Pointwise quantum ordering on morphisms                       *)
(* ================================================================== *)
(*
    The hom-set [X →qc Y] carries a natural "pointwise quantum order":

      F ⊑_q G  iff  ∀ x, q_top ⊑ R_Y(F x, G x)

    This is the Prop-valued ordering that makes the set of quantum-
    continuous maps a classical partial order (and ultimately a CPO).

    - Reflexivity:   from qp_refl on Y.
    - Transitivity:  from qp_trans on Y + q_prod_mono_l + q_prod_top_l.
    - Antisymmetry:  q_hom_le f g ∧ q_hom_le g f implies equal
                     quantum orders (we state the order-equality form).

    KLM Theorem 3.3.5 uses this ordering to show that the hom-sets
    form CPOs.
*)

Section HomOrder.

Context {X Y : qposet Q}.

Definition q_hom_le (f g : [X →qc Y]) : Prop :=
    forall (x : X), (q_top : Q) ⊑ qp_ord Y (qcf_fun f x) (qcf_fun g x).

Lemma q_hom_le_refl (f : [X →qc Y]) : q_hom_le f f.
Proof.
    intro x.
    apply qp_refl.
Qed.

Lemma q_hom_le_trans (f g h : [X →qc Y]) :
    q_hom_le f g -> q_hom_le g h -> q_hom_le f h.
Proof.
    intros Hfg Hgh x.
    (* q_top ⊑ R(Fx, Gx) ⊗ R(Gx, Hx) ⊑ R(Fx, Hx) *)
    apply @le_trans with
        (y := qp_ord Y (qcf_fun f x) (qcf_fun g x)
              ⊗ qp_ord Y (qcf_fun g x) (qcf_fun h x)).
    - (* q_top ⊑ R(Fx,Gx) ⊗ R(Gx,Hx) *)
      assert (Hstep : (q_top : Q) ⊗ qp_ord Y (g x) (h x)
                       ⊑ qp_ord Y (f x) (g x) ⊗ qp_ord Y (g x) (h x)).
      { apply q_prod_mono_l. exact (Hfg x). }
      assert (Htop : (q_top : Q) ⊗ qp_ord Y (g x) (h x) = qp_ord Y (g x) (h x)).
      { exact (q_prod_top_l _). }
      rewrite Htop in Hstep.
      apply @le_trans with (y := qp_ord Y (qcf_fun g x) (qcf_fun h x)).
      + exact (Hgh x).
      + exact Hstep.
    - apply qp_trans.
Qed.

(*
    Order-equality form: if F ⊑ G and G ⊑ F, their quantum orders
    to any third element agree.
*)
Lemma q_hom_le_antisym_ord (f g : [X →qc Y]) :
    q_hom_le f g -> q_hom_le g f ->
    forall (x : X) (y : Y),
        qp_ord Y (qcf_fun f x) y = qp_ord Y (qcf_fun g x) y.
Proof.
    intros Hfg Hgf x y.
    apply (@le_antisym Q).
    - apply qp_antitone_l. exact (Hgf x).
    - apply qp_antitone_l. exact (Hfg x).
Qed.

End HomOrder.


(* ================================================================== *)
(*  §10 CPO-enrichment of hom-sets                                    *)
(* ================================================================== *)
(*
    For quantum CPOs X and Y, a chain of quantum-continuous maps
      F₁ ⊑_q F₂ ⊑_q F₃ ⊑_q ...
    (ascending in the pointwise quantum order) has a pointwise limit
    F∞ that is also quantum-continuous.

    This is the quantum analogue of [fun_sup_continuous] from
    FunctionSpaces.v and is the core of KLM Theorem 3.3.5.

    The hom-ascending condition says:
      ∀ n x, q_top ⊑ R_Y(Fs(n)(x), Fs(S n)(x))

    which is exactly qchain_ascending for the sequence
    n ↦ (fun w => Fs n w), treating X as the probe type W.
*)

Section HomChainLimit.

Context {X Y : qposet Q}.

(*
    A "hom-chain" is a sequence of quantum-continuous maps
    F₁ ⊑_q F₂ ⊑_q ... ascending in the pointwise quantum order.

    This directly gives qchain_ascending with W = X.
*)
Definition hom_qchain
    (Fs : nat -> [X →qc Y])
    (Hle : forall (n : nat) (x : X),
        (q_top : Q) ⊑ qp_ord Y (Fs n x) (Fs (S n) x)) :
    @qchain Q Y X :=
    Build_qchain (fun n x => Fs n x) Hle.

(*
    Given QCPOData on Y (with probe type X), the hom-chain converges
    and we can extract the pointwise limit.
*)
Definition qhom_limit
    (Fs : nat -> [X →qc Y])
    (Hle : forall (n : nat) (x : X),
        (q_top : Q) ⊑ qp_ord Y (Fs n x) (Fs (S n) x))
    (D : @QCPOData Q Y X) : X -> Y :=
    qlimit D (hom_qchain Fs Hle).

(*
    The pointwise limit of a hom-chain is an upper bound:
    each Fs(n) is below the limit.
*)
Lemma qhom_limit_upper
    (Fs : nat -> [X →qc Y])
    (Hle : forall (n : nat) (x : X),
        (q_top : Q) ⊑ qp_ord Y (Fs n x) (Fs (S n) x))
    (D : @QCPOData Q Y X) :
    forall (n : nat) (x : X),
        (q_top : Q) ⊑ qp_ord Y (Fs n x) (qhom_limit Fs Hle D x).
Proof.
    intros n x.
    unfold qhom_limit.
    apply converges_upper_top with (K := hom_qchain Fs Hle).
    apply qlimit_converges.
Qed.

(*
    The pointwise limit is Scott-continuous (monotonicity part).

    If each Fs(n) is monotone, the pointwise limit inherits
    monotonicity: for all x x',
      R_X(x, x') ⊑ R_Y(Fs n x, Fs n x') ⊑ ...
    and the limit preserves this.
*)
Lemma qhom_limit_mono
    (Fs : nat -> [X →qc Y])
    (Hle : forall (n : nat) (x : X),
        (q_top : Q) ⊑ qp_ord Y (Fs n x) (Fs (S n) x))
    (D : @QCPOData Q Y X) :
    q_monotone (qhom_limit Fs Hle D).
Proof.
    intros x x'.
    unfold qhom_limit.
    set (lim := qlimit D (hom_qchain Fs Hle)).
    pose proof (qlimit_converges D (hom_qchain Fs Hle)) as Hconv.
    (* R(lim x, lim x') = inf_n R(Fs n x, lim x') by convergence *)
    apply @le_trans with
        (y := q_inf (qord_desc_chain (hom_qchain Fs Hle) x (lim x'))).
    - (* R_X(x,x') ⊑ inf_n R_Y(Fs n x, lim x') *)
      apply q_inf_greatest. intro n. simpl.
      (* R_X(x,x') ⊑ R_Y(Fs n x, lim x') *)
      apply @le_trans with (y := qp_ord Y (Fs n x) (Fs n x')).
      + exact (qcf_mono (Fs n) x x').
      + apply qp_covariant_r.
        exact (qhom_limit_upper Fs Hle D n x').
    - exact (proj2 (Hconv x (lim x'))).
Qed.

(*
    The pointwise limit is Scott-continuous (convergence part).
*)
(*
    Proof structure — double q_inf_lower + q_inf_greatest.

    ⊑ direction: monotonicity of lim + converges_upper_top + qp_antitone_l.

    ⊒ direction: for each m and n',
        inf_{n'} R(lim(K(n',w)), x)
          ⊑ R(lim(K(n',w)), x)                     [q_inf_lower at n']
          ⊑ inf_m R(Fs(m)(K(n',w)), x)              [hom convergence proj1]
          ⊑ R(Fs(m)(K(n',w)), x)                    [q_inf_lower at m]
    Then q_inf_greatest over n' ⟹ ⊑ inf_{n'} R(Fs(m)(K(n',w)), x),
    then Fs(m) continuity proj2 ⟹ ⊑ R(Fs(m)(K_inf w), x),
    then q_inf_greatest over m ⟹ ⊑ inf_m R(Fs(m)(K_inf w), x),
    then hom convergence proj2 ⟹ ⊑ R(lim(K_inf w), x).
*)
Lemma qhom_limit_preserves
    (Fs : nat -> [X →qc Y])
    (Hle : forall (n : nat) (x : X),
        (q_top : Q) ⊑ qp_ord Y (Fs n x) (Fs (S n) x))
    (D : @QCPOData Q Y X) :
    forall (W : Type) (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        converges
            (map_qchain (qhom_limit Fs Hle D) (qhom_limit_mono Fs Hle D) K)
            (fun w => qhom_limit Fs Hle D (K_inf w)).
Proof.
    intros W K K_inf Hconv.
    pose proof (qlimit_converges D (hom_qchain Fs Hle)) as Hhom.
    set (lim := qhom_limit Fs Hle D).
    set (Hlim := qhom_limit_mono Fs Hle D).
    intros w x. split.
    - (* ⊑: R(lim(K_inf w), x) ⊑ inf_{n'} R(lim(K(n',w)), x)
         Each K(n',w) ⊑ K_inf(w) by converges_upper_top, and lim
         is monotone, so lim(K(n',w)) ⊑ lim(K_inf w); then antitone_l. *)
      apply q_inf_greatest. intro n'. simpl.
      apply qp_antitone_l.
      apply @le_trans with (y := qp_ord X (qch K n' w) (K_inf w)).
      + exact (converges_upper_top K K_inf Hconv n' w).
      + exact (Hlim (qch K n' w) (K_inf w)).
    - (* ⊒: inf_{n'} R(lim(K(n',w)), x) ⊑ R(lim(K_inf w), x)
         Transit through inf_m R(Fs(m)(K_inf w), x). *)
      apply @le_trans with
          (y := q_inf (qord_desc_chain (hom_qchain Fs Hle) (K_inf w) x)).
      + (* inf_{n'} R(lim(K(n',w)), x) ⊑ inf_m R(Fs(m)(K_inf w), x) *)
        apply q_inf_greatest. intro m. simpl.
        (* Goal: inf_{n'} R(lim(K(n',w)), x) ⊑ R(Fs(m)(K_inf w), x) *)
        apply @le_trans with
            (y := q_inf (qord_desc_chain
                    (map_qchain (qcf_fun (Fs m)) (qcf_mono (Fs m)) K) w x)).
        * (* inf_outer ⊑ inf_{n'} R(Fs(m)(K(n',w)), x) *)
          apply q_inf_greatest. intro n'. simpl.
          (* Thread: q_inf_lower at n' then hom conv then q_inf_lower at m *)
          apply @le_trans with (y := qp_ord Y (lim (qch K n' w)) x).
          -- exact (q_inf_lower
                (qord_desc_chain (map_qchain lim Hlim K) w x) n').
          -- apply @le_trans with
                (y := q_inf (qord_desc_chain
                        (hom_qchain Fs Hle) (qch K n' w) x)).
             ++ exact (proj1 (Hhom (qch K n' w) x)).
             ++ exact (q_inf_lower
                    (qord_desc_chain (hom_qchain Fs Hle) (qch K n' w) x) m).
        * (* inf_{n'} R(Fs(m)(K(n',w)), x) ⊑ R(Fs(m)(K_inf w), x) *)
          exact (proj2 (qcf_preserves (Fs m) W K K_inf Hconv w x)).
      + (* inf_m R(Fs(m)(K_inf w), x) ⊑ R(lim(K_inf w), x) *)
        exact (proj2 (Hhom (K_inf w) x)).
Qed.

(*
    Bundled: the pointwise limit of a hom-chain is a q_cont_fun.
*)
Definition qhom_limit_cont
    (Fs : nat -> [X →qc Y])
    (Hle : forall (n : nat) (x : X),
        (q_top : Q) ⊑ qp_ord Y (Fs n x) (Fs (S n) x))
    (D : @QCPOData Q Y X) : [X →qc Y] :=
    Build_q_cont_fun
        (qhom_limit Fs Hle D)
        (qhom_limit_mono Fs Hle D)
        (qhom_limit_preserves Fs Hle D).

End HomChainLimit.


(* ================================================================== *)
(*  §11 Kleene fixed point for pointed quantum CPOs                   *)
(* ================================================================== *)
(*
    Given a pointed quantum CPO (X, R, ⊥) with QCPOData and a
    Scott-continuous endomorphism F : X → X, the iteration sequence:

      ⊥, F(⊥), F²(⊥), F³(⊥), ...

    forms a quantum chain (ascending), and its limit [qfixp F] is
    the least fixed point of F.

    This is the quantum analogue of the Kleene fixed-point theorem
    from FixedPoints.v.

    The argument:
    (1) ⊥ ⊑_q F(⊥) because ⊥ is bottom: q_top ⊑ R(⊥, F⊥)
    (2) F^n(⊥) ⊑_q F^{n+1}(⊥) by induction using monotonicity
    (3) The sequence converges by QCPOData
    (4) The limit is a fixed point by continuity of F
    (5) The limit is least among prefixed points
*)

Section KleeneFixedPoint.

Context {X : qposet Q} (bot : QBottom (X := X))
        (W : Type) (D : @QCPOData Q X W).

(*  Iteration: F^n(⊥) *)
Fixpoint q_iter (F : [X →qc X]) (n : nat) : X :=
    match n with
    | O   => q_bot_elem bot
    | S k => F (q_iter F k)
    end.

Lemma q_iter_zero (F : [X →qc X]) : q_iter F 0 = q_bot_elem bot.
Proof. reflexivity. Qed.

Lemma q_iter_succ (F : [X →qc X]) (n : nat) :
    q_iter F (S n) = F (q_iter F n).
Proof. reflexivity. Qed.

(*  The iteration sequence is ascending in the quantum order. *)
Lemma q_iter_ascending (F : [X →qc X]) (n : nat) (w : W) :
    (q_top : Q) ⊑ qp_ord X (q_iter F n) (q_iter F (S n)).
Proof.
    induction n.
    - (* 0: q_top ⊑ R(⊥, F(⊥)) — by bottom property *)
      simpl. apply q_bot_proof.
    - (* S n: q_top ⊑ R(F(iter n), F(iter (S n))) — by monotonicity *)
      simpl.
      apply @le_trans with (y := qp_ord X (q_iter F n) (q_iter F (S n))).
      + exact IHn.
      + apply qcf_mono.
Qed.

(*  Package iteration as a qchain.  The chain is constant in w
    (the iteration doesn't depend on the probe). *)
Definition q_kleene_chain (F : [X →qc X]) : @qchain Q X W :=
    Build_qchain
        (fun n (_ : W) => q_iter F n)
        (fun n w => q_iter_ascending F n w).

(*  The Kleene fixed point is the limit of the iteration chain,
    evaluated at any (dummy) probe element.  Since the chain is
    constant in W, the limit is also constant in W — we extract
    one value via an arbitrary w₀ : W.

    For the important case W = unit (which suffices for the
    fixed-point theorem), we use tt as the probe. *)

(*  Version requiring an element of W to extract the fixed point. *)
Definition qfixp_at (F : [X →qc X]) (w0 : W) : X :=
    qlimit D (q_kleene_chain F) w0.

(*  The limit at any two probe elements agrees.  Because the chain is
    constant in W, the desc-chains at w₁ and w₂ have definitionally
    equal dch fields, so their infima agree. *)
Lemma qfixp_at_const (F : [X →qc X]) (w1 w2 : W) (y : X) :
    qp_ord X (qfixp_at F w1) y = qp_ord X (qfixp_at F w2) y.
Proof.
    unfold qfixp_at.
    pose proof (qlimit_converges D (q_kleene_chain F)) as Hconv.
    set (d1 := qord_desc_chain (q_kleene_chain F) w1 y).
    set (d2 := qord_desc_chain (q_kleene_chain F) w2 y).
    (* dch d1 n ≡ dch d2 n definitionally, so their infima agree. *)
    assert (H12 : q_inf d1 ⊑ q_inf d2).
    { apply q_inf_greatest. intro n. exact (q_inf_lower d1 n). }
    assert (H21 : q_inf d2 ⊑ q_inf d1).
    { apply q_inf_greatest. intro n. exact (q_inf_lower d2 n). }
    pose proof (@le_antisym Q _ _ H12 H21) as Hinf.
    apply (@le_antisym Q).
    - apply @le_trans with (y := q_inf d2).
      + rewrite <- Hinf. exact (proj1 (Hconv w1 y)).
      + exact (proj2 (Hconv w2 y)).
    - apply @le_trans with (y := q_inf d1).
      + rewrite Hinf. exact (proj1 (Hconv w2 y)).
      + exact (proj2 (Hconv w1 y)).
Qed.

(*  F(fixp) is the fixed point in the quantum order.

    Proof idea: the mapped chain F∘K (where K is the Kleene chain)
    and the cofinal subchain K∘S have the same underlying sequence
    (both give n ↦ q_iter F (S n)).  By cofinal_converges, K∘S
    converges to K_inf.  By converges_ext, F∘K also converges to
    K_inf.  But by continuity of F, F∘K converges to F∘K_inf.
    By uniqueness of limits, F∘K_inf = K_inf. *)
Lemma qfixp_at_is_fixedpoint (F : [X →qc X]) (w0 : W) :
    forall (y : X),
        qp_ord X (qcf_fun F (qfixp_at F w0)) y =
        qp_ord X (qfixp_at F w0) y.
Proof.
    intro y.
    unfold qfixp_at.
    set (K := q_kleene_chain F).
    set (K_inf := qlimit D K).
    pose proof (qlimit_converges D K) as Hconv.
    (* S is strictly monotone *)
    assert (Hphi : strict_mono S).
    { intro n. unfold lt. apply le_n. }
    (* By cofinal_converges, K∘S converges to K_inf *)
    pose proof (cofinal_converges K K_inf S Hphi Hconv) as Hcof.
    (* cofinal_qchain K S has the same values as map_qchain F K *)
    assert (Heq : forall n w,
        qch (cofinal_qchain K S Hphi) n w =
        qch (map_qchain (qcf_fun F) (qcf_mono F) K) n w).
    { intros n w. reflexivity. }
    (* By converges_ext, map_qchain F K converges to K_inf *)
    pose proof (converges_ext
        (cofinal_qchain K S Hphi)
        (map_qchain (qcf_fun F) (qcf_mono F) K)
        K_inf Heq Hcof) as Hmap2.
    (* By continuity of F, map_qchain F K converges to F∘K_inf *)
    pose proof (qcf_preserves F W K K_inf Hconv) as Hmap1.
    (* By uniqueness: R(F(K_inf w), y) = R(K_inf w, y) *)
    exact (converges_unique
        (map_qchain (qcf_fun F) (qcf_mono F) K)
        (fun w => qcf_fun F (K_inf w)) K_inf
        Hmap1 Hmap2 w0 y).
Qed.

(*  fixp is the least prefixed point.

    If x is a PREfixed point (F(x) ⊑ x in the enriched sense),
    then fixp ⊑ x.  The enriched form of F(x) ⊑ x is:
      ∀ y, R(x, y) ⊑ R(F(x), y)
    (by antitonicity of R in the first argument).

    Proof: By induction, q_iter F n ⊑ x for all n.
    Then by antitone_l + convergence, fixp ⊑ x. *)
Lemma qfixp_at_least (F : [X →qc X]) (w0 : W) (x : X) :
    (forall y : X, qp_ord X x y ⊑ qp_ord X (qcf_fun F x) y) ->
    forall y : X, qp_ord X x y ⊑ qp_ord X (qfixp_at F w0) y.
Proof.
    intros Hpre y.
    unfold qfixp_at.
    set (K := q_kleene_chain F).
    pose proof (qlimit_converges D K) as Hconv.
    (* Step 1: Extract Prop-level F(x) ⊑ x *)
    assert (Hfx : (q_top : Q) ⊑ qp_ord X (qcf_fun F x) x).
    { apply @le_trans with (y := qp_ord X x x).
      - apply qp_refl.
      - exact (Hpre x). }
    (* Step 2: By induction, q_iter F n ⊑ x for all n *)
    assert (Hiter : forall n, (q_top : Q) ⊑ qp_ord X (q_iter F n) x).
    { intro n. induction n.
      - simpl. apply q_bot_proof.
      - simpl.
        (* Need: q_top ⊑ R(F(iter n), x) *)
        (* From IHn: iter n ⊑ x → F(iter n) ⊑ F(x) by mono.
           From Hfx: F(x) ⊑ x.
           By antitone_l: R(F(x),x) ⊑ R(F(iter n), x). *)
        apply @le_trans with (y := qp_ord X (qcf_fun F x) x).
        + exact Hfx.
        + apply qp_antitone_l.
          apply @le_trans with (y := qp_ord X (q_iter F n) x).
          * exact IHn.
          * exact (qcf_mono F (q_iter F n) x). }
    (* Step 3: By antitone_l, R(x,y) ⊑ R(q_iter F n, y) for all n *)
    (* Step 4: By q_inf_greatest + convergence *)
    apply @le_trans with
        (y := q_inf (qord_desc_chain K w0 y)).
    - apply q_inf_greatest. intro n. simpl.
      apply qp_antitone_l.
      exact (Hiter n).
    - exact (proj2 (Hconv w0 y)).
Qed.

(*  Scott induction for quantum fixed points. *)
Definition q_admissible (P : X -> Prop) : Prop :=
    forall (K : @qchain Q X W) (K_inf : W -> X),
        converges K K_inf ->
        (forall n w, P (qch K n w)) ->
        forall w, P (K_inf w).

Lemma qfixp_at_ind (F : [X →qc X]) (w0 : W) (P : X -> Prop) :
    q_admissible P ->
    P (q_bot_elem bot) ->
    (forall x, P x -> P (F x)) ->
    P (qfixp_at F w0).
Proof.
    intros Hadm Hbot Hstep.
    unfold qfixp_at.
    apply (Hadm (q_kleene_chain F) (qlimit D (q_kleene_chain F))).
    - apply qlimit_converges.
    - intros n w. simpl.
      induction n.
      + exact Hbot.
      + apply Hstep. exact IHn.
Qed.

End KleeneFixedPoint.

End QContFun.
