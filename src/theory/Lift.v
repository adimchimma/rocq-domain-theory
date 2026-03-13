(*  Lift

    Phase 0: The flat lift [⟨D⟩⊥] of a CPO [D].

    This is [src/theory/Lift.v].

    Imports:
      [src/structures/Order.v]     — Preorder, PartialOrder, chain, mono_fun
      [src/structures/CPO.v]       — CPO, PointedCPO
      [src/structures/Morphisms.v] — cont_fun, cont_comp, cont_id
      [src/theory/OrderTheory.v]   — le_antisym, le_trans
      [src/theory/ChainTheory.v]   — ch_mono, chain_zero_le
      [src/theory/CPOTheory.v]     — sup_upper, sup_least, sup_ext,
                                     le_sup_of_le_elem

    Summary
    =======
    The _flat lift_ [⟨D⟩⊥] of a CPO [D] is the type [option D] under the order:

        None    ⊑ x          for all x         (None is the unique fresh bottom)
        Some d  ⊑ Some d'    iff d ⊑[D] d'
        Some d  ⊑ None       = False

    This adds a single new bottom element [⊥ = None] strictly below every
    element [Some d].  The sup of a chain [c] is computed classically:

    - If [∀ n, c.[n] = None]: then [⊔ c = None].
    - If [∃ N, c.[N] ≠ None]: the chain stabilises in [Some] from [N] onward.
      The sup is [⊔ c = Some (⊔ (D_chain N d₀ c HN))] where [D_chain]
      extracts the [D]-values from the tail [k ↦ c.[N + k]].

    This construction uses [ClassicalEpsilon], which strictly extends the
    [Classical] axiom already used in the library.  The coinductive
    [delay]-based alternative is developed in [LiftMonad.v], together with
    a precise statement of why that type cannot be a [CPO.type] without
    quotient types.

    Contents:
    - §1  Lift order — HB instance registrations
    - §2  Auxiliary — value extraction, chain stability, [D_chain]
    - §3  Lift sup — [HasSup] and [IsCPO] instances;
              [lift_sup_some_eq] and [PointedCPO] instances
    - §4  The unit [ret : D →c ⟨D⟩⊥]
    - §5  Kleisli extension [kleisli f : ⟨D⟩⊥ →c ⟨E⟩⊥]
    - §6  Monad laws

    References: A&J §2.1.4; Moggi (1991); Benton-Kennedy-Varming (2009) §2.2.
*)

From HB Require Import structures.
From Stdlib Require Import ClassicalEpsilon.
From DomainTheory.Structures Require Import Order CPO Morphisms.
From DomainTheory.Theory Require Import OrderTheory ChainTheory CPOTheory.

From Stdlib Require Import Arith.


(* ================================================================== *)
(* §1  Lift order                                                     *)
(* ================================================================== *)

Section LiftOrder.
Context {D : CPO.type}.

(*
    [None] is the fresh bottom; [Some d ⊑ Some d'] tracks the [D]-order;
    [Some _ ⊑ None] is [False].
*)
Definition lift_le (x y : option D) : Prop :=
  match x, y with
  | None,   _       => True
  | Some d, Some d' => d ⊑ d'
  | Some _, None    => False
  end.

Lemma lift_le_refl (x : option D) : lift_le x x.
Proof.
  destruct x; simpl; [exact (le_refl _) | exact I].
Qed.

Lemma lift_le_trans (x y z : option D) :
    lift_le x y -> lift_le y z -> lift_le x z.
Proof.
  destruct x, y, z; simpl; try tauto.
  exact (le_trans _ _ _).
Qed.

Lemma lift_le_antisym (x y : option D) :
    lift_le x y -> lift_le y x -> x = y.
Proof.
  destruct x, y; simpl; try tauto.
  intros Hxy Hyx; f_equal; exact (le_antisym _ _ Hxy Hyx).
Qed.

End LiftOrder.

HB.instance Definition lift_HasLe {D : CPO.type} :=
  HasLe.Build (option D) lift_le.

HB.instance Definition lift_IsPreorder {D : CPO.type} :=
  IsPreorder.Build (option D) lift_le_refl lift_le_trans.

HB.instance Definition lift_IsPartialOrder {D : CPO.type} :=
  IsPartialOrder.Build (option D) lift_le_antisym.

(* Postfix notation: [⟨D⟩⊥] for [option D], the flat lift of [D].
   Angle brackets distinguish this from the standalone [⊥] notation
   (the bottom element from [CPO.v]).
   At level 0 with argument at level 99 — the same level and first-
   argument level as the pairing notation [⟨f, g⟩] from [Products.v],
   so both share a compatible prefix.  The parser disambiguates by
   the second token: [,] for pairing vs [⟩⊥] for lifting.
       chain ⟨D⟩⊥      mono_fun ⟨D⟩⊥ ⟨E⟩⊥      [⟨D⟩⊥ →c ⟨E⟩⊥]
   Available to any file that imports [Lift.v]. *)
Notation "⟨ D ⟩⊥" := (option D)
  (at level 0, D at level 99, format "⟨ D ⟩⊥").

(* Convenience unfolding lemmas. *)
Lemma lift_le_some_iff {D : CPO.type} (d d' : D) :
    (Some d : ⟨D⟩⊥) ⊑ Some d' <-> d ⊑ d'.
Proof.
  reflexivity.
Qed.

Lemma lift_none_le {D : CPO.type} (x : ⟨D⟩⊥) : (None : ⟨D⟩⊥) ⊑ x.
Proof.
  exact I.
Qed.

Lemma lift_some_not_le_none {D : CPO.type} (d : D) :
    ~ (Some d : ⟨D⟩⊥) ⊑ None.
Proof.
  exact id.
Qed.


(* ================================================================== *)
(* §2  Auxiliary: extraction, chain stability, D-chain                *)
(* ================================================================== *)

Section LiftAux.
Context {D : CPO.type}.

(*
    Recover the [D]-value from a term known to be [Some _].
    References:
      https://www.unwoundstack.com/blog/dependent-matching-in-coq.html
*)
Definition extract_some (x : ⟨D⟩⊥) (H : x <> None) : D :=
  match x as y return y <> None -> D with
  | Some d => fun _  => d
  | None   => fun H  => False_rect D (H eq_refl)
  end H.

Lemma some_of_extract (x : ⟨D⟩⊥) (H : x <> None) :
    x = Some (extract_some x H).
Proof.
  destruct x; [reflexivity| contradiction].
Qed.

(*
    Once a chain reaches [Some], it never returns to [None].
    If [c.[N] = Some _] and [c.[N + k] = None] then
    [c.[N] ⊑ c.[N+k]] gives [Some _ ⊑ None = False].
*)
Lemma chain_some_stable (c : chain ⟨D⟩⊥) (N k : nat)
    (HN : c.[N] <> None) : c.[N + k] <> None.
Proof.
  intros Heq.
  pose proof (ch_mono c N (N + k) (Nat.le_add_r N k)) as Hle.
  rewrite (some_of_extract (c.[N]) HN), Heq in Hle.
  exact Hle.
Qed.

Lemma chain_some_stable_le (c : chain ⟨D⟩⊥) (N m : nat)
    (HN : c.[N] <> None) (HNm : N <= m) : c.[m] <> None.
Proof.
  pose proof (chain_some_stable c N (m - N) HN).
  rewrite (Arith_base.le_plus_minus_stt N m HNm); exact H.
Qed.

(*
    The [D]-chain extracted from a converged chain.

        D_chain_fn N d₀ c k  =  the D-value inside c.[N + k]

    The default [d₀] is only used in the vacuous [None] branch (which is
    never reached for [k ≥ 0] when [HN : c.[N] <> None]).
*)
Definition D_chain_fn (N : nat) (d₀ : D) (c : chain ⟨D⟩⊥) (k : nat) : D :=
  match c.[N + k] with Some d => d | None => d₀ end.

(*
    The [None] branch is unreachable: [c.[N + k] = Some (D_chain_fn ...)].
*)
Lemma D_chain_fn_eq (N : nat) (d₀ : D) (c : chain ⟨D⟩⊥) (k : nat)
    (HN : c.[N] <> None) :
    c.[N + k] = Some (D_chain_fn N d₀ c k).
Proof.
  unfold D_chain_fn.
  pose proof (chain_some_stable c N k HN).
  destruct (c.[N + k]); [reflexivity | contradiction].
Qed.

(*
    [D_chain_fn] is monotone.

    Proof: use [D_chain_fn_eq] to equate [D_chain_fn ... m] and [D_chain_fn ... n]
    with [c.[N+m]] and [c.[N+n]] inside the ambient [option D] order, where
    [Some a ⊑ Some b] is definitionally [a ⊑ b].
*)
Lemma D_chain_mono (N : nat) (d₀ : D) (c : chain ⟨D⟩⊥)
    (HN : c.[N] <> None) : forall m n : nat, m <= n ->
    D_chain_fn N d₀ c m ⊑ D_chain_fn N d₀ c n.
Proof.
  intros m n Hmn.
  pose proof (ch_mono c (N + m) (N + n) (proj1 (Nat.add_le_mono_l m n N) Hmn)) as Hle.
  rewrite (D_chain_fn_eq N d₀ c m HN) in Hle.
  rewrite (D_chain_fn_eq N d₀ c n HN) in Hle.
  exact Hle.
Qed.

Definition D_chain (N : nat) (d₀ : D) (c : chain ⟨D⟩⊥)
    (HN : c.[N] <> None) : chain D :=
  Build_chain (D_chain_fn N d₀ c) (D_chain_mono N d₀ c HN).

End LiftAux.


(* ================================================================== *)
(* §3  Lift sup                                                       *)
(* ================================================================== *)
(*
    We use [excluded_middle_informative] to decide whether the chain
    ever leaves [None], and [constructive_indefinite_description] to
    extract a stabilisation index [N].

    The choice of [N] is immaterial: any two witnesses give the same sup
    (forced by [sup_least] uniqueness).

    [lift_sup_upper] for the [Some] branch:
    - [n ≥ N]: [c.[n] = Some (D_chain_fn N d₀ c (n-N))], which is ⊑ ⊔ D_chain. ✓
    - [n < N]: [c.[n] ⊑ c.[N] = Some d₀ = Some D_chain.[0]], so ⊑ ⊔ D_chain. ✓

    [lift_sup_least] for [p = Some e]:
    For each [k]: [Hub (N+k) : c.[N+k] ⊑ Some e], which after substituting
    [c.[N+k] = Some (D_chain_fn ... k)] gives [D_chain_fn ... k ⊑ e]. ✓
*)

Section LiftSup.
Context {D : CPO.type}.

Definition lift_sup (c : chain ⟨D⟩⊥) : ⟨D⟩⊥ :=
  match excluded_middle_informative (exists n, c.[n] <> None) with
  | right _   => None
  | left  Hex =>
    let '(exist _ N HN) := constructive_indefinite_description _ Hex in
    let d₀ := extract_some (c.[N]) HN in
    Some (⊔ D_chain N d₀ c HN)
  end.

Lemma lift_sup_none (c : chain ⟨D⟩⊥) (Hall : forall n, c.[n] = None) :
    lift_sup c = None.
Proof.
  unfold lift_sup.
  destruct (excluded_middle_informative _) as [Hex | _]; [|reflexivity].
  destruct Hex as [n Hn].
  exfalso; apply Hn.
  exact (Hall n).
Qed.

Lemma lift_sup_upper (c : chain ⟨D⟩⊥) (n : nat) :
    c.[n] ⊑ lift_sup c.
Proof.
  unfold lift_sup.
  destruct (excluded_middle_informative _) as [Hex | Hall].
  - destruct (constructive_indefinite_description _ Hex) as [N HN].
    set (d₀ := extract_some (c.[N]) HN).
    pose proof (some_of_extract (c.[N]) HN) as HcN.
    destruct (c.[n]) eqn:Hn.
    + destruct (Nat.le_decidable N n) as [HNn | HnN].
      * apply le_sup_of_le_elem with (n := n - N).
        simpl; unfold D_chain_fn.
        rewrite (Arith_base.le_plus_minus_stt N n HNn) in Hn.
        rewrite Hn.
        exact (le_refl s).
      * apply not_le in HnN.
        pose proof (ch_mono c n N (Nat.lt_le_incl n N HnN)) as Hle.
        rewrite Hn, HcN in Hle.
        apply le_sup_of_le_elem with (n := 0).
        simpl; unfold D_chain_fn.
        rewrite (Nat.add_0_r N), HcN.
        exact Hle.
      + exact I.
  - destruct (c.[n]) eqn:Hn; [| exact I].
    exfalso; apply Hall.
    exists n. rewrite Hn; discriminate.
Qed. 

Lemma lift_sup_least (c : chain ⟨D⟩⊥) (p : ⟨D⟩⊥) :
    (forall n, c.[n] ⊑ p) -> lift_sup c ⊑ p.
Proof.
  intros Hub.
  unfold lift_sup.
  destruct (excluded_middle_informative _) as [Hex | _].
  - destruct (constructive_indefinite_description _ Hex) as [N HN].
    set (d₀ := extract_some (c.[N]) HN).
    destruct p as [e |].
    + apply sup_least; intros k.
      simpl.
      pose proof (Hub (N + k)) as Hbn.
      rewrite (D_chain_fn_eq N d₀ c k HN) in Hbn.
      exact Hbn.
    + pose proof (Hub N) as Hbn.
      rewrite (some_of_extract (c.[N]) HN) in Hbn.
      exact Hbn.
  - exact I.
Qed.

End LiftSup.

HB.instance Definition lift_HasSup {D : CPO.type} :=
  HasSup.Build ⟨D⟩⊥ lift_sup.

HB.instance Definition lift_IsCPO {D : CPO.type} :=
  IsCPO.Build ⟨D⟩⊥ lift_sup_upper lift_sup_least.

HB.instance Definition lift_HasBottom {D : CPO.type} :=
  HasBottom.Build ⟨D⟩⊥ (@None D).

Section LiftBottom.
Context {D : CPO.type}.

Lemma lift_bottom_least (x : ⟨D⟩⊥) : (⊥ : ⟨D⟩⊥) ⊑ x.
Proof.
  exact I.
Qed.

End LiftBottom.

HB.instance Definition lift_IsPointed {D : CPO.type} :=
  IsPointed.Build ⟨D⟩⊥ lift_bottom_least.

Lemma lift_bottom_none {D : CPO.type} : (⊥ : ⟨D⟩⊥) = None.
Proof.
  reflexivity.
Qed.

(*
    ----------------------------------------------------------------
    Key computation lemma: when a chain has reached [Some] at index [N],
    the supremum is [Some (⊔ D_chain N d₀ c HN)].

    This holds for _any_ default value [d₀] and _any_ witness [N]
    satisfying [c.[N] <> None].  The D-chain values are independent of
    [d₀] (the [None] branch in [D_chain_fn] is unreachable), so different
    witnesses give the same supremum value.

    This lemma is used as the main rewriting step in §4 and §5.
    ----------------------------------------------------------------
*)
Section LiftSupSomeEq.
Context {D : CPO.type}.

Lemma lift_sup_some_eq (c : chain ⟨D⟩⊥) (N : nat) (d₀ : D)
    (HN : c.[N] <> None) :
    ⊔ c = Some (⊔ D_chain N d₀ c HN).
Proof.
  apply le_antisym.
  - (* Forward: ⊔ c ⊑ Some (⊔ D_chain N d₀ c HN) *)
    apply @sup_least; intros n.
    destruct (c.[n]) eqn:Hn; simpl.
    + destruct (Nat.le_decidable N n) as [HNn | HnN].
      * (* n ≥ N: c.[n] = Some s sits in D_chain at index n - N *)
        eapply (le_trans _ (Some s) _).
        { rewrite <- Hn. apply le_refl. }
        refine (le_sup_of_le_elem (D_chain N d₀ c HN) s (n - N) _).
        pose proof (D_chain_fn_eq N d₀ c (n - N) HN) as Htail.
        replace (N + (n - N)) with n in Htail.
        2: { exact (Arith_base.le_plus_minus_stt N n HNn). }
        pose proof (eq_trans (eq_sym Hn) Htail) as Hs.
        injection Hs as ->.
        simpl. exact (le_refl _).
      * (* n < N: s ⊑ extract_some c.[N] = D_chain.[0] ⊑ ⊔ D_chain *)
        apply not_le in HnN.
        pose proof (some_of_extract (c.[N]) HN) as HcN.
        pose proof (ch_mono c n N (Nat.lt_le_incl n N HnN)) as Hle.
        rewrite Hn, HcN in Hle.
        eapply (le_trans _ (Some s) _).
        { rewrite <- Hn. apply le_refl. }
        eapply (le_trans _ (Some (extract_some c.[N] HN)) _).
        { exact Hle. }
        refine (le_sup_of_le_elem (D_chain N d₀ c HN)
                    (extract_some (c.[N]) HN) 0 _).
        pose proof (D_chain_fn_eq N d₀ c 0 HN) as H0.
        replace (N + 0) with N in H0.
        2: { symmetry. exact (Nat.add_0_r N). }
        pose proof (eq_trans (eq_sym HcN) H0) as Hextract.
        injection Hextract as ->.
        unfold D_chain; simpl. exact (le_refl _).
    + exact (eq_ind None
                (fun x => x ⊑ Some (⊔ D_chain N d₀ c HN))
                I c.[n] (eq_sym Hn)).
  - (* Backward: Some (⊔ D_chain N d₀ c HN) ⊑ ⊔ c *)
    destruct (⊔ c) as [u |] eqn:Hsup.
    + apply sup_least; intros k.
      pose proof (sup_upper c (N + k)) as HNk.
      pose proof (eq_ind (⊔ c)
                    (fun y => c.[N + k] ⊑ y)
                    HNk (Some u) Hsup) as HNk_sup.
      pose proof (D_chain_fn_eq N d₀ c k HN) as Heqk.
      pose proof (eq_ind (c.[N + k])
                    (fun x => x ⊑ Some u)
                    HNk_sup (Some (D_chain_fn N d₀ c k)) Heqk) as HNk_dchain.
      exact HNk_dchain.
    + exfalso.
      pose proof (sup_upper c N) as HNsup.
      pose proof (eq_ind (⊔ c)
                    (fun y => c.[N] ⊑ y)
                    HNsup None Hsup) as HNsup1.
      rewrite (some_of_extract (c.[N]) HN) in HNsup1.
      exact HNsup1.
Qed.

End LiftSupSomeEq.


(* ================================================================== *)
(* §4  The unit [ret : D →c ⟨D⟩⊥]                                      *)
(* ================================================================== *)
(*
    [ret d := Some d].  Monotonicity: immediate from the lift order.

    Continuity: we need [ret (⊔ c) = ⊔ (map_chain ret_mono c)],
    i.e., [Some (⊔ c) = ⊔ (map_chain ret_mono c)].

    The chain [map_chain ret_mono c = n ↦ Some(c.[n])] always stays in [Some]
    (index [0] is [Some (c.[0]) ≠ None]).  Applying [lift_sup_some_eq] with
    [N = 0] and [d₀ = c.[0]] gives
    [⊔ (map_chain ret_mono c) = Some (⊔ D_chain 0 (c.[0]) (map_chain ret_mono c) _)].
    Since [D_chain_fn 0 (c.[0]) (map_chain ret_mono c) k = c.[k]], the inner
    supremum equals [⊔ c].  The result follows by [sup_ext].
*)
Section LiftUnit.
Context {D : CPO.type}.

Definition ret_mono : mono_fun D ⟨D⟩⊥ :=
  Build_mono_fun Some (fun d d' H => H).

Lemma continuous_ret : continuous ret_mono.
Proof.
  intros c.
  assert (HN0 : (map_chain ret_mono c).[0] <> None).
  - simpl. discriminate.
  - pose proof (lift_sup_some_eq (map_chain ret_mono c) 0 (c.[0]) HN0) as Hsup.
    eapply eq_trans.
    2: exact (eq_sym Hsup).
    apply f_equal.
    apply sup_ext; intro k.
    simpl; unfold D_chain_fn; simpl.
    reflexivity.
Qed.

Definition ret : [D →c ⟨D⟩⊥] :=
  Build_cont_fun ret_mono continuous_ret.

Lemma ret_some (d : D) : ret d = Some d.
Proof.
  reflexivity.
Qed.

End LiftUnit.


(* ================================================================== *)
(* §5  Kleisli extension [kleisli f : ⟨D⟩⊥ →c ⟨E⟩⊥]                    *)
(* ================================================================== *)
(*
    [kleisli f None     = None]
    [kleisli f (Some d) = f d]

    Continuity (eventually-[Some] case):
    Since [c.[N] ≠ None], apply [lift_sup_some_eq] to rewrite [⊔ c].
    The goal reduces to [f (⊔ D_chain) = ⊔ (map_chain (kleisli f) c)].
    Use continuity of [f] on the left, then show the two chains are
    pointwise equal by an index shift:
    - LHS chain: [(map_chain f D_chain).[k] = f (D_chain_fn N d₀ c k)]
    - RHS chain: [(map_chain (kleisli f) c).[N + k] = f (D_chain_fn N d₀ c k)]
    For indices [n < N]: [kleisli f (c.[n]) ⊑ kleisli f (c.[N]) = f d₀ = f D_chain.[0]].
*)

Section LiftKleisli.
Context {D E : CPO.type}.

Definition kleisli_fun (f : [D →c ⟨E⟩⊥]) (x : ⟨D⟩⊥) : ⟨E⟩⊥ :=
  match x with Some d => f d | None => None end.

Lemma kleisli_mono (f : [D →c ⟨E⟩⊥]) :
    monotone ⟨D⟩⊥ ⟨E⟩⊥ (kleisli_fun f).
Proof.
  intros x y Hxy.
  destruct x, y; simpl in *.
  - apply (cf_mono f). exact Hxy.
  - exact (False_ind _ Hxy).
  - exact I.
  - exact I.
Qed.

Definition kleisli_mfun (f : [D →c ⟨E⟩⊥]) : mono_fun ⟨D⟩⊥ ⟨E⟩⊥ :=
  Build_mono_fun (kleisli_fun f) (kleisli_mono f).

(*
    Index-shift equality: [(map_chain (kleisli f) c).[N+k] = (map_chain f D_chain).[k]].
*)
Lemma kleisli_map_chain_shift_eq
    (f : [D →c ⟨E⟩⊥]) (c : chain ⟨D⟩⊥)
    (N : nat) (d₀ : D) (HN : c.[N] <> None) (k : nat) :
    (map_chain (kleisli_mfun f) c).[N + k] =
    (map_chain (cf_mono f) (D_chain N d₀ c HN)).[k].
Proof.
  simpl. unfold kleisli_fun.
  destruct (c.[N + k]) eqn:Hc.
  - f_equal.
    pose proof (D_chain_fn_eq N d₀ c k HN) as HD.
    pose proof (eq_trans (eq_sym Hc) HD) as Hsd.
    inversion Hsd; reflexivity.
  - pose proof (chain_some_stable c N k HN).
    contradiction.
Qed.

Lemma continuous_kleisli (f : [D →c ⟨E⟩⊥]) :
    continuous (kleisli_mfun f).
Proof.
  intros c.
  destruct (excluded_middle_informative (exists n, c.[n] <> None)) as [Hex | Hall].
  - destruct (constructive_indefinite_description _ Hex) as [N HN].
    set (d₀ := extract_some (c.[N]) HN).
    pose proof (lift_sup_some_eq c N d₀ HN) as Hsupc.
    assert (Hleft : kleisli_fun f (⊔ c) = f (⊔ D_chain N d₀ c HN)).
    { unfold kleisli_fun.
      refine (eq_ind_r
                (fun x => kleisli_fun f x = f (⊔ D_chain N d₀ c HN))
                _ Hsupc).
      reflexivity. }
    eapply eq_trans.
    + exact Hleft.
    + eapply eq_trans.
      * exact (cf_cont f (D_chain N d₀ c HN)).
      * eapply eq_trans.
        -- apply sup_ext; intro k.
           rewrite chain_shift_index.
           rewrite (Nat.add_comm k N).
           symmetry.
           exact (kleisli_map_chain_shift_eq f c N d₀ HN k).
        -- apply sup_shift.
  - assert (HallEq : forall n, c.[n] = None).
    { intro n.
      destruct (c.[n]) eqn:Hn; [| reflexivity].
      exfalso. apply Hall. exists n. rewrite Hn. discriminate. }
    assert (HallK : forall n, (map_chain (kleisli_mfun f) c).[n] = None).
    { intro n.
      simpl. unfold kleisli_fun.
      destruct (c.[n]) eqn:Hn.
      - rewrite (HallEq n) in Hn.
        discriminate.
      - refine (eq_ind_r
                  (fun x => match x with Some d => f d | None => None end = None)
                  _ Hn).
        reflexivity. }
    pose proof (lift_sup_none c HallEq) as Hsupc.
    pose proof (lift_sup_none (map_chain (kleisli_mfun f) c) HallK) as Hsupk.
    assert (HleftNone : kleisli_fun f (⊔ c) = None).
    { unfold kleisli_fun.
      refine (eq_ind_r (fun x => kleisli_fun f x = None) _ Hsupc).
      reflexivity. }
    eapply eq_trans.
    + exact HleftNone.
    + exact (eq_sym Hsupk).
Qed.

Definition kleisli (f : [D →c ⟨E⟩⊥]) : [⟨D⟩⊥ →c ⟨E⟩⊥] :=
  Build_cont_fun (kleisli_mfun f) (continuous_kleisli f).

Lemma kleisli_none (f : [D →c ⟨E⟩⊥]) : kleisli f None = None.
Proof.
  reflexivity.
Qed.

Lemma kleisli_some (f : [D →c ⟨E⟩⊥]) (d : D) : kleisli f (Some d) = f d.
Proof.
  reflexivity.
Qed.

End LiftKleisli.


(* ================================================================== *)
(* §6  Monad laws                                                     *)
(* ================================================================== *)

Section LiftMonadLaws.
Context {D E F : CPO.type}.

(* (ML1) Left unit: [kleisli f ∘ ret = f] *)
Lemma kleisli_ret_left (f : [D →c ⟨E⟩⊥]) :
    cont_comp (kleisli f) (ret (D := D)) = f.
Proof.
  apply cont_fun_ext; intros; reflexivity.
Qed.

(* (ML2) Right unit: [kleisli ret = id] *)
Lemma kleisli_ret_right :
    kleisli (ret (D := D)) = cont_id ⟨D⟩⊥.
Proof.
  apply cont_fun_ext; intros x.
  destruct x; reflexivity.
Qed.

(* (ML3) Associativity: [kleisli g ∘ kleisli f = kleisli (kleisli g ∘ f)] *)
Lemma kleisli_assoc (f : [D →c ⟨E⟩⊥]) (g : [E →c ⟨F⟩⊥]) :
    cont_comp (kleisli g) (kleisli f) =
    kleisli (cont_comp (kleisli g) f).
Proof.
  apply cont_fun_ext; intros x.
  destruct x; reflexivity.
Qed.

(*
    [kleisli] is monotone in its argument.
*)
Lemma kleisli_mono_fun (f g : [D →c ⟨E⟩⊥])
    (Hle : forall d, f d ⊑ g d) :
    forall x : ⟨D⟩⊥, kleisli f x ⊑ kleisli g x.
Proof.
  intros x; destruct x; simpl; [exact (Hle s) | exact I].
Qed.

(*
    Kleisli composition.
*)
Lemma kleisli_comp_cont {G : CPO.type}
    (f : [D →c ⟨E⟩⊥]) (g : [E →c ⟨G⟩⊥]) (x : ⟨D⟩⊥) :
    kleisli g (kleisli f x) = kleisli (cont_comp (kleisli g) f) x.
Proof.
  destruct x; reflexivity.
Qed.

End LiftMonadLaws.