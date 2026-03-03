(*  ChainTheory

    Phase 0: Derived theory for omega-chains.

    This is [src/theory/ChainTheory.v].  It imports only [Order.v] and
    [OrderTheory.v]; no CPO, no sup.  Supremum-dependent chain lemmas
    (e.g. "the sup of an eventually-constant chain is its limit") belong
    in [CPOTheory.v].

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/theory/OrderTheory.v]   — pequiv_*, chain_*, map_chain_*

    Contents:
    - §1  Chain shift — [chain_shift k c], generalising [tail_chain]
    - §2  Eventually-constant chains — [eventually_const], structural lemmas
    - §3  Classical stabilisation — monotone boolean predicates on chains
    - §4  Coherent chain families — the diagonal construction for [FunctionSpaces.v]
    - §5  Reindexing and miscellaneous chain combinators

    Phase coverage:
      Phase 0 — all sections
      Phase 1 — §4 (coherent families) used in enriched function-space proofs
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order.
From DomainTheory.Theory Require Import OrderTheory.

From Stdlib Require Import Classical PeanoNat Lia.


(* ================================================================== *)
(*   §1  Chain shift                                                  *)
(* ================================================================== *)
(*
    [chain_shift k c] is the chain [n ↦ c.[n + k]], i.e. the chain [c]
    with its first [k] elements discarded.  [tail_chain] in [Order.v]
    is the special case [k = 1].

    Shifting is the key technical tool in eventually-constant chain
    arguments: once we know that [c] stabilises from index [N], we work
    with [chain_shift N c] which is constant from index [0]. 
*)

Definition chain_shift {P : Preorder.type} (k : nat) (c : chain P) : chain P :=
  Build_chain
    (fun n => c.[n + k])
    (fun m n Hmn => ch_mono c (m + k) (n + k) (proj1 (Nat.add_le_mono_r m n k) Hmn)).

Arguments chain_shift {P} k c.

Section ChainShiftLemmas.
Context {P : Preorder.type}.

(* Unfolding the index of a shifted chain. *)
Lemma chain_shift_index (k : nat) (c : chain P) (n : nat) :
    (chain_shift k c).[n] = c.[n + k].
Proof.
  reflexivity.
Qed.

(* [chain_shift 0] agrees with the original chain at every index. *)
Lemma chain_shift_zero (c : chain P) (n : nat) :
    (chain_shift 0 c).[n] = c.[n].
Proof.
  simpl.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

(*
    Shifting by a successor equals taking the tail of the chain shifted by [k].
    Both sides reduce to [c.[S (n + k)]]:
      LHS: [c.[n + S k]] = [c.[S (n + k)]] by [Nat.add_succ_r]
      RHS: [c.[S n + k]] = [c.[S (n + k)]] by [Nat.succ_add]
*)
Lemma chain_shift_succ (k : nat) (c : chain P) (n : nat) :
    (chain_shift (S k) c).[n] = (tail_chain (chain_shift k c)).[n].
Proof.
  simpl.
  rewrite Nat.add_succ_r.
  reflexivity.
Qed.

(* Shifting by [k] then by [j] equals shifting by [k + j]. *)
Lemma chain_shift_add (j k : nat) (c : chain P) (n : nat) :
    (chain_shift j (chain_shift k c)).[n] = (chain_shift (k + j) c).[n].
Proof.
  simpl.
  f_equal.
  lia.
Qed.

(* A shift is above the original at every index (since [n ≤ n + k]). *)
Lemma chain_shift_ge (k : nat) (c : chain P) (n : nat) :
    c.[n] ⊑ (chain_shift k c).[n].
Proof.
  simpl.
  apply ch_mono.
  exact (Nat.le_add_r n k).
Qed.

(* [map_chain] and [chain_shift] commute (definitionally equal). *)
Lemma map_chain_shift {Q : Preorder.type} (f : mono_fun P Q)
    (k : nat) (c : chain P) (n : nat) :
    (map_chain f (chain_shift k c)).[n] = (chain_shift k (map_chain f c)).[n].
Proof.
  reflexivity.
Qed.

End ChainShiftLemmas.


(* ================================================================== *)
(*   §2  Eventually-constant chains                                   *)
(* ================================================================== *)
(*
    A chain [c] is _eventually constant at [x]_ if all elements from
    some index [N] onward equal [x].

    This is the key concept for [Sums.v]: a chain in [A ⊕ B] must
    eventually stabilise in one summand (since the sum order makes
    cross-comparisons [False]), and once it has, its sup is the sup of
    the projected chain in that summand.

    Note: the sup of an eventually-constant chain equals [x], but this
    requires [sup_upper] / [sup_least] and therefore lives in [CPOTheory.v].
    This section only proves structural properties. 
*)
Definition eventually_const {P : Preorder.type} (c : chain P) (x : P) : Prop :=
  exists N : nat, forall n : nat, N <= n -> c.[n] = x.

Section EventuallyConstLemmas.
Context {P : Preorder.type}.

(* If [c] stabilises at [x] from index [N], then [c.[N] = x]. *)
Lemma eventually_const_at_witness (c : chain P) (x : P) (N : nat) :
    (forall n, N <= n -> c.[n] = x) -> c.[N] = x.
Proof.
  intros H; exact (H N (Nat.le_refl N)).
Qed.

(* A constant chain is eventually constant from index 0. *)
Lemma const_chain_eventually_const (x : P) :
    eventually_const (const_chain x) x.
Proof.
  exists 0; intros n _; reflexivity.
Qed.

(* [tail_chain] preserves eventual constancy. *)
Lemma eventually_const_tail (c : chain P) (x : P) :
    eventually_const c x -> eventually_const (tail_chain c) x.
Proof.
  intros [N HN].
  exists N; intros n Hge.
  rewrite tail_chain_index.
  apply HN.
  apply le_S.
  exact Hge.
Qed.

(* [chain_shift k] preserves eventual constancy. *)
Lemma eventually_const_shift (k : nat) (c : chain P) (x : P) :
    eventually_const c x -> eventually_const (chain_shift k c) x.
Proof.
  intros [N HN].
  exists N; intros n Hge.
  rewrite chain_shift_index.
  apply HN.
  apply (Nat.le_trans N n (n + k)).
  - exact Hge.
  - exact (Nat.le_add_r n k).
Qed.

(* Eventual constancy is preserved when the witness index is raised. *)
Lemma eventually_const_weaken (c : chain P) (x : P) (N M : nat) :
    N <= M ->
    (forall n, N <= n -> c.[n] = x) ->
    (forall n, M <= n -> c.[n] = x).
Proof.
  intros HNM HN n Hn.
  apply HN.
  exact (Nat.le_trans N M n HNM Hn).
Qed.

(* Eventual constancy is preserved under [map_chain]. *)
Lemma eventually_const_map {Q : Preorder.type} (f : mono_fun P Q)
    (c : chain P) (x : P) :
    eventually_const c x -> eventually_const (map_chain f c) (f x).
Proof.
  intros [N HN].
  exists N; intros n Hge.
  simpl.
  rewrite (HN n Hge).
  reflexivity.
Qed.

(*
    From the stabilisation index on, every element satisfies both ⊑ x and ⊒ x. 
*)
Lemma eventually_const_le_ge (c : chain P) (x : P) :
    eventually_const c x ->
    exists N, forall n, N <= n -> c.[n] ⊑ x /\ x ⊑ c.[n].
Proof.
  intros [N HN].
  exists N; intros n Hge.
  rewrite (HN n Hge).
  split; exact (le_refl x).
Qed.

End EventuallyConstLemmas.

(*
    In a partial order, an eventually-constant chain has a unique limit. 
*)
Lemma eventually_const_unique {P : PartialOrder.type} (c : chain P) (x y : P) :
    eventually_const c x -> eventually_const c y -> x = y.
Proof.
  intros [Nx HNx] [Ny HNy].
  set (N := Nat.max Nx Ny).
  assert (HcN_x : c.[N] = x) by exact (HNx N (Nat.le_max_l Nx Ny)).
  assert (HcN_y : c.[N] = y) by exact (HNy N (Nat.le_max_r Nx Ny)).
  exact (eq_trans (eq_sym HcN_x) HcN_y).
Qed.


(* ================================================================== *)
(*   §3  Classical stabilisation for monotone boolean predicates      *)
(* ================================================================== *)
(*
    Key tool for [Sums.v]: in a sum CPO, chain elements cannot change
    "side" (from [inl] to [inr]) because the sum order makes such
    comparisons [False].  The general form is: an upward-closed boolean
    predicate [φ] on a chain either stabilises to [true] eventually, or
    is always [false].

    We use [Classical] (imported above) for the initial case split.
*)
Section ClassicalStabilisation.
Context {P : Preorder.type}.

(*
    Upward-closed [φ]: either eventually always [true], or always [false]. 
    Reference: https://ncatlab.org/nlab/show/filter
*)
Lemma chain_pred_stabilises
    (φ : P -> bool)
    (Hmono : forall x y : P, x ⊑ y -> φ x = true -> φ y = true)
    (c : chain P) :
    (exists N, forall n, N <= n -> φ (c.[n]) = true) \/
    (forall n, φ (c.[n]) = false).
Proof.
  destruct (classic (exists n, φ (c.[n]) = true)) as [[N HN] | Hnone].
  - left; exists N.
    intros n Hge.
    exact (Hmono (c.[N]) c.[n] (ch_mono c N n Hge) HN).
  - right; intros n.
    destruct (φ c.[n]) eqn:Heq; [|reflexivity].
    exfalso.
    apply Hnone.
    exact (ex_intro (fun k => φ c.[k] = true) n Heq).
Qed.

(*
    Upward-closed [φ = false] (once false on the chain, stays false further up):
    either eventually always [false], or always [true].

    Note: [Hmono] here has the same direction as in [chain_pred_stabilises] —
    both propagate their respective value *forward* along [⊑].  The original
    backwards formulation ([φ y = false -> φ x = false]) was equivalent to
    [Hup] (they are contrapositives in bool) and so useless for forward
    propagation. 
*)
Lemma chain_pred_stabilises_false
    (φ : P -> bool)
    (Hmono : forall x y : P, x ⊑ y -> φ x = false -> φ y = false)
    (c : chain P) :
    (exists N, forall n, N <= n -> φ (c.[n]) = false) \/
    (forall n, φ (c.[n]) = true).
Proof.
  destruct (classic (exists n, φ (c.[n]) = false)) as [[N HN] | Hnone].
  - left; exists N.
    intros n Hge.
    exact (Hmono c.[N] c.[n] (ch_mono c N n Hge) HN).
  - right; intros n.
    destruct (φ (c.[n])) eqn:Heq; [reflexivity|].
    exfalso.
    apply Hnone.
    exact (ex_intro (fun k => φ (c.[k]) = false) n Heq).
Qed.

(*
    Once a chain element satisfies an upward-closed [φ], all subsequent
    elements do too.  (No classical reasoning needed here.) 
*)
Lemma chain_mono_pred_from
    (φ : P -> bool)
    (Hmono : forall x y : P, x ⊑ y -> φ x = true -> φ y = true)
    (c : chain P) (N : nat) :
    φ (c.[N]) = true -> forall n, N <= n -> φ (c.[n]) = true.
Proof.
  intros Hpred n Hge.
  exact (Hmono c.[N] c.[n] (ch_mono c N n Hge) Hpred).
Qed.

(*
    Symmetric version for [false]: once false, stays false forward.
    (No classical reasoning needed here either.) 
*)
Lemma chain_mono_pred_from_false
    (φ : P -> bool)
    (Hmono : forall x y : P, x ⊑ y -> φ x = false -> φ y = false)
    (c : chain P) (N : nat) :
    φ (c.[N]) = false -> forall n, N <= n -> φ (c.[n]) = false.
Proof.
  intros HN n Hn.
  exact (Hmono (c.[N]) (c.[n]) (ch_mono c N n Hn) HN).
Qed.

(*
    [chain_pred_dichotomy]: when both [true] and [false] propagate
    forward along [⊑], the predicate is constant on the entire chain.

    Both hypotheses push their value in the same direction (upward along
    the chain).  Together they make [φ] constant: the value of [φ (c.[0])]
    determines all subsequent values.

    This is the version directly used in [Sums.v] with [φ = is_left]:
    in the sum order, once a chain element is [inl], all later ones must
    be [inl] too (and likewise for [inr]).

    Note: no classical reasoning is required — just case-split on [φ (c.[0])].
    The earlier proof via [Nat.le_or_lt] was not only more complex but
    was broken: [Hdown] as originally stated ([φ y = false -> φ x = false])
    is the contrapositive of [Hup], making both hypotheses redundant and
    leaving the n ≤ N branch unprovable. 
*)
Lemma chain_pred_dichotomy
    (φ : P -> bool)
    (Hup   : forall x y : P, x ⊑ y -> φ x = true  -> φ y = true)
    (Hdown : forall x y : P, x ⊑ y -> φ x = false -> φ y = false)
    (c : chain P) :
    (forall n, φ (c.[n]) = true) \/
    (forall n, φ (c.[n]) = false).
Proof.
  destruct (φ (c.[0])) eqn:H0.
  - left; intros n.
    exact (chain_mono_pred_from φ Hup c 0 H0 n (Nat.le_0_l n)).
  - right; intros n.
    pose proof chain_mono_pred_from_false.
    exact (chain_mono_pred_from_false φ Hdown c 0 H0 n (Nat.le_0_l n)).
Qed.

End ClassicalStabilisation.


(* ================================================================== *)
(*   §4  Coherent chain families (diagonal construction)              *)
(* ================================================================== *)
(*
    The _diagonal chain_ construction is used in [FunctionSpaces.v] to
    prove that [D ⇒ E] (the function-space CPO) is a CPO.

    A family of chains [F : nat -> chain E] is _coherent_ if it is
    pointwise non-decreasing in the family index:
      [F m . [k] ⊑ F n . [k]]   whenever [m ≤ n].

    Under coherence, the diagonal [n ↦ (F n).[n]] is itself a chain:
      [(F m).[m] ⊑ (F m).[n]]   (within row m, since m ≤ n)
      [(F m).[n] ⊑ (F n).[n]]   (coherence across rows)
    so [(F m).[m] ⊑ (F n).[n]] by transitivity.

    In [FunctionSpaces.v], [F n] = [map_chain (cf_mono f_n) d] where
    [f_n] is a chain of continuous functions. 
*)

Definition coherent_family {E : Preorder.type} (F : nat -> chain E) : Prop :=
  forall m n k, m <= n -> (F m).[k] ⊑ (F n).[k].

Section CoherentFamilyLemmas.
Context {E : Preorder.type}.

Lemma diag_mono (F : nat -> chain E) (Hcoh : coherent_family F) :
    forall m n : nat, m <= n -> (F m).[m] ⊑ (F n).[n].
Proof.
  intros m n Hle.
  apply le_trans with ((F m).[n]).
  - exact (ch_mono (F m) m n Hle).
  - exact (Hcoh m n n Hle).
Qed.

Definition diag_chain (F : nat -> chain E) (Hcoh : coherent_family F) : chain E :=
  Build_chain (fun n => (F n).[n]) (diag_mono F Hcoh).

Lemma diag_chain_index (F : nat -> chain E) (Hcoh : coherent_family F) (n : nat) :
    (diag_chain F Hcoh).[n] = (F n).[n].
Proof.
  reflexivity.
Qed.

(*
    The diagonal lies below the [n]-th row at column [k] when [n ≤ k]. 
*)
Lemma diag_below_row (F : nat -> chain E) (Hcoh : coherent_family F)
    (n k : nat) (Hnk : n <= k) :
    (diag_chain F Hcoh).[n] ⊑ (F n).[k].
Proof.
  rewrite diag_chain_index.
  exact (ch_mono (F n) n k Hnk).
Qed.

(*
    The diagonal lies below column [k] of row [n] when [k ≤ n] (by coherence). 
*)
Lemma diag_below_col (F : nat -> chain E) (Hcoh : coherent_family F)
    (k n : nat) (Hkn : k <= n) :
    (diag_chain F Hcoh).[k] ⊑ (F n).[k].
Proof.
  rewrite diag_chain_index.
  unfold coherent_family in Hcoh.
  exact (Hcoh k n k Hkn).
Qed.

(* Mapping a monotone function over each row preserves coherence. *)
Lemma coherent_family_map {Q : Preorder.type} (f : mono_fun E Q)
    (F : nat -> chain E) (Hcoh : coherent_family F) :
    coherent_family (fun n => map_chain f (F n)).
Proof.
  intros n m k HnLEm.
  simpl.
  exact (mf_mono f _ _ (Hcoh n m k HnLEm)).
Qed.

(* A constant family (same chain at every index) is trivially coherent. *)
Lemma coherent_family_const (c : chain E) : coherent_family (fun _ => c).
Proof.
  intros n m k _; apply le_refl.
Qed.

(*
    Pointwise inequality between two coherent families implies pointwise
    inequality between their diagonals. 
*)
Lemma diag_chain_le (F G : nat -> chain E)
    (HcohF : coherent_family F) (HcohG : coherent_family G)
    (Hle : forall m k, (F m).[k] ⊑ (G m).[k]) :
    forall n, (diag_chain F HcohF).[n] ⊑ (diag_chain G HcohG).[n].
Proof.
  intros n.
  do 2 rewrite diag_chain_index.
  exact (Hle n n).
Qed.

End CoherentFamilyLemmas.


(* ================================================================== *)
(*   §5  Reindexing and miscellaneous chain combinators               *)
(* ================================================================== *)

Section ChainCombinators.

(*
    [chain_reindex c σ Hσ]: compose the underlying function of [c] with
    a monotone [σ : ℕ → ℕ].  Subsumes [chain_shift] (σ n = n + k) and
    [tail_chain] (σ n = S n).
*)
Definition chain_reindex {P : Preorder.type}
    (c : chain P) (σ : nat -> nat)
    (Hσ : forall m n, m <= n -> σ m <= σ n) : chain P :=
  Build_chain
    (fun n => c.[σ n])
    (fun m n Hmn => ch_mono c (σ m) (σ n) (Hσ m n Hmn)).

Lemma chain_reindex_index {P : Preorder.type}
    (c : chain P) (σ : nat -> nat) (Hσ : forall m n, m <= n -> σ m <= σ n)
    (n : nat) :
    (chain_reindex c σ Hσ).[n] = c.[σ n].
Proof.
  reflexivity.
Qed.

(* A reindexed chain lies above the original when [n ≤ σ n]. *)
Lemma chain_reindex_ge {P : Preorder.type}
    (c : chain P) (σ : nat -> nat) (Hσ : forall m n, m <= n -> σ m <= σ n)
    (Hσn : forall n, n <= σ n) (n : nat) :
    c.[n] ⊑ (chain_reindex c σ Hσ).[n].
Proof.
  rewrite chain_reindex_index.
  exact (ch_mono c n (σ n) (Hσn n)).
Qed.

(** [chain_shift] is a special case of [chain_reindex]. *)
Lemma chain_shift_as_reindex {P : Preorder.type} (k : nat) (c : chain P) (n : nat) :
    (chain_shift k c).[n] =
    (chain_reindex c (fun m => m + k) (fun m n Hmn => (proj1 (Nat.add_le_mono_r m n k) Hmn))).[n].
Proof.
  reflexivity.
Qed.

(*
    [chain_from N c] is a descriptive alias for [chain_shift N c], used
    in proofs that fix a stabilisation witness [N] and want to name the
    "suffix" of the chain explicitly. 
*)
Definition chain_from {P : Preorder.type} (N : nat) (c : chain P) : chain P :=
  chain_shift N c.

Lemma chain_from_index {P : Preorder.type} (N : nat) (c : chain P) (n : nat) :
    (chain_from N c).[n] = c.[n + N].
Proof.
  reflexivity.
Qed.

End ChainCombinators.