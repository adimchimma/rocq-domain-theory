(*  Discrete CPOs

    Phase 0: The unit PointedCPO and discrete CPOs for arbitrary types.

    This is [src/instances/Discrete.v].

    A _discrete_ CPO on a type [A] carries the equality order:
        x ⊑ y  ↔  x = y.
    Since the only monotone sequences under equality are constant ones,
    every chain has a supremum [c.[0]].  Discrete CPOs model ground-type
    semantics: there is no "approximation" between distinct values of the
    same base type.  Partiality is added separately by the lift [option D].

    [unit] is registered with the *trivial* order ([x ⊑ y := True]),
    which coincides with the discrete order on a one-element type but
    requires no case analysis in proofs.  [unit] is a [PointedCPO] with
    [tt] as the unique (and least) element.  It denotes the empty typing
    context in [PCF_Denotational.v].

    Contents:
    - §1  Unit PointedCPO
    - §2  Generic discrete CPO ([Discrete A] newtype + HB instances)
    - §3  Bool discrete CPO (direct HB registration on [bool])

    Imports:
      [src/structures/Order.v]     — HasLe, IsPreorder, IsPartialOrder, chain
      [src/structures/CPO.v]       — HasSup, IsCPO, HasBottom, IsPointed
      [src/theory/CPOTheory.v]     — sup_unique

    Note on [nat]:
      [nat] as a CPO uses the same discrete pattern and is registered
      separately in [src/instances/Nat.v] to avoid HB instance conflicts.

    Phase coverage:
      Phase 0 — all sections
      Used by [PCF_Denotational.v] for [sem_env []] (unit) and [sem_ty Bool]
      (bool).  [Discrete A] is available for examples and tests.

    References:
      Abramsky & Jung §2.1.2 (discrete CPOs as flat ground-type domains).
      Benton & Kennedy §3 (denotational semantics of PCFv ground types).
*)

From HB Require Import structures.
From DomainTheory.Structures Require Import Order CPO.
From DomainTheory.Theory Require Import CPOTheory.


(* ================================================================== *)
(*   §1  Unit PointedCPO                                              *)
(* ================================================================== *)
(*
    [unit] with the trivial order [_ ⊑ _ := True].

    Since [unit] has exactly one element, the trivial and equality orders
    coincide.  We use the trivial order so that [⊑] proofs are always [I].

    Structure:
      Order:   x ⊑ y  :=  True         (always holds)
      Sup:     ⊔ c    :=  tt            (the only element)
      Bottom:  ⊥      :=  tt
      Least:   ⊥ ⊑ x  :=  I

    HB ordering constraint (CPO.v §DD-008):
      [IsPointed] requires [of CPO T & HasBottom T], so [HasBottom] and
      [IsPointed] must be registered after [IsCPO].
*)

Section UnitOrder.

Definition unit_le : unit -> unit -> Prop := fun _ _ => True.

Lemma unit_le_refl (x : unit) : unit_le x x.
Proof. 
  exact I.
Qed.

Lemma unit_le_trans (x y z : unit) :
    unit_le x y -> unit_le y z -> unit_le x z. 
Proof. 
  intros _ _; exact I.
Qed.

Lemma unit_le_antisym (x y : unit) :
    unit_le x y -> unit_le y x -> x = y.
Proof.
  destruct x, y; intros; reflexivity.
Qed.

End UnitOrder.

HB.instance Definition unit_HasLe :=
  HasLe.Build unit unit_le.

HB.instance Definition unit_IsPreorder :=
  IsPreorder.Build unit unit_le_refl unit_le_trans.

HB.instance Definition unit_IsPartialOrder :=
  IsPartialOrder.Build unit unit_le_antisym.

Section UnitSup.

Definition unit_sup (_ : chain unit) : unit := tt.

Lemma unit_sup_upper (c : chain unit) (n : nat) : c.[n] ⊑ unit_sup c.
Proof.
  exact I.
Qed.

Lemma unit_sup_least (c : chain unit) (x : unit)
    (_ : forall n, c.[n] ⊑ x) : unit_sup c ⊑ x.
Proof.
  exact I.
Qed.

End UnitSup.

HB.instance Definition unit_HasSup :=
  HasSup.Build unit unit_sup.

HB.instance Definition unit_IsCPO :=
  IsCPO.Build unit unit_sup_upper unit_sup_least.

(*  HB DD-008: HasBottom and IsPointed after IsCPO. *)
HB.instance Definition unit_HasBottom :=
  HasBottom.Build unit tt.

Lemma unit_bottom_least (x : unit) : (⊥ : unit) ⊑ x.
Proof.
  exact I.
Qed.

HB.instance Definition unit_IsPointed :=
  IsPointed.Build unit unit_bottom_least.

(*  The sup of any chain in [unit] is [tt]. *)
Lemma unit_sup_tt (c : chain unit) : ⊔ c = tt.
Proof. 
  reflexivity. 
Qed.

(*
    Every monotone function out of [unit] is Scott-continuous.

    Proof: the unique element of a chain in [unit] is [tt], so the chain
    is constant.  [sup_unique] closes the goal using [sup_upper] at 0.
*)
Lemma unit_continuous_any {D : CPO.type} (f : mono_fun unit D) :
    continuous f.
Proof.
  intro c.
  (* ⊔ c = tt = c.[0]; all chain elements are tt. *)
  rewrite unit_sup_tt.
  apply sup_unique.
  - intro n. simpl. destruct (c.[n]). apply le_refl.
  - assert (H0 : c.[0] = tt).
    { destruct (c.[0]); reflexivity. }
    rewrite <- H0.
    change ((map_chain f c).[0] ⊑ ⊔ map_chain f c).
    exact (sup_upper (map_chain f c) 0).
Qed.


(* ================================================================== *)
(*   §2  Generic discrete CPO ([Discrete A])                          *)
(* ================================================================== *)
(*
    We wrap [A] in a newtype [Discrete A] to avoid HB instance conflicts
    with other CPO structures that may be registered on [A] (e.g. the
    usual [≤] order on [nat] in [Nat.v]).

    API:
      [Discrete A]            — the newtype carrier
      [disc a : Discrete A]   — constructor (wraps a value)
      [undisc x : A]          — destructor / projection
      [disc_undisc]           — [undisc (disc a) = a]     (left inverse)
      [undisc_disc]           — [disc (undisc x) = x]     (right inverse)

    Structure:
      Order:  x ⊑ y  :=  x = y          (discrete: only reflexive pairs)
      Sup:    ⊔ c    :=  c.[0]           (constant chains)

    Key lemma [disc_chain_const]:
      [ch_mono c 0 n (Nat.le_0_l n) : c.[0] ⊑ c.[n]]
      In the discrete order this is [c.[0] = c.[n]].
      Symmetry gives [c.[n] = c.[0]].

    Note: [Discrete A] is NOT a [PointedCPO] unless [A] is inhabited
    (there is no canonical least element for an arbitrary type).
*)

Record Discrete (A : Type) : Type := disc { undisc : A }.

Arguments disc   {A} _.
Arguments undisc {A} _.

Lemma disc_undisc {A : Type} (a : A) : undisc (disc a) = a.
Proof. 
  reflexivity. 
Qed.

Lemma undisc_disc {A : Type} (x : Discrete A) : disc (undisc x) = x.
Proof. 
  destruct x; reflexivity. 
Qed.

Section DiscOrder.
Variable A : Type.

Definition disc_le (x y : Discrete A) : Prop := x = y.

Lemma disc_le_refl (x : Discrete A) : disc_le x x.
Proof. 
  reflexivity. 
Qed.

Lemma disc_le_trans (x y z : Discrete A) :
    disc_le x y -> disc_le y z -> disc_le x z.
Proof. 
  intros ->; tauto. 
Qed.

Lemma disc_le_antisym (x y : Discrete A) :
    disc_le x y -> disc_le y x -> x = y.
Proof. 
  intros H _; exact H. 
Qed.

End DiscOrder.

HB.instance Definition disc_HasLe (A : Type) :=
  HasLe.Build (Discrete A) (disc_le A).

HB.instance Definition disc_IsPreorder (A : Type) :=
  IsPreorder.Build (Discrete A) (disc_le_refl A) (disc_le_trans A).

HB.instance Definition disc_IsPartialOrder (A : Type) :=
  IsPartialOrder.Build (Discrete A) (disc_le_antisym A).

Section DiscSup.
Variable A : Type.

(*
    Every chain in [Discrete A] is constant.

    [ch_mono c 0 n (Nat.le_0_l n) : c.[0] ⊑ c.[n]]
    In the discrete order [⊑ = =], this is [c.[0] = c.[n]].
    Symmetry: [c.[n] = c.[0]].
*)
Lemma disc_chain_const (c : chain (Discrete A)) (n : nat) :
    c.[n] = c.[0].
Proof.
  symmetry.
  exact (ch_mono c 0 n (PeanoNat.Nat.le_0_l n)).
Qed.

Definition disc_sup (c : chain (Discrete A)) : Discrete A := c.[0].

(*
    Upper bound: [c.[n] = c.[0] = disc_sup c].
    In the discrete order, [=] IS [⊑].
*)
Lemma disc_sup_upper (c : chain (Discrete A)) (n : nat) :
    c.[n] ⊑ disc_sup c.
Proof.
  unfold disc_sup.
  exact (disc_chain_const c n).
Qed.

(*
    Least upper bound: [disc_sup c = c.[0]], and [c.[0] ⊑ x] by [Hub 0].
*)
Lemma disc_sup_least (c : chain (Discrete A)) (x : Discrete A)
    (Hub : forall n, c.[n] ⊑ x) : disc_sup c ⊑ x.
Proof.
  unfold disc_sup.
  exact (Hub 0).
Qed.

End DiscSup.

HB.instance Definition disc_HasSup (A : Type) :=
  HasSup.Build (Discrete A) (disc_sup A).

HB.instance Definition disc_IsCPO (A : Type) :=
  IsCPO.Build (Discrete A) (disc_sup_upper A) (disc_sup_least A).

(*  Computation rule: [⊔ c = c.[0]] in [Discrete A]. *)
Lemma disc_sup_eq {A : Type} (c : chain (Discrete A)) :
    ⊔ c = c.[0].
Proof. 
  reflexivity. 
Qed.

(*
    Every monotone function out of [Discrete A] is Scott-continuous.

    Proof: [⊔ c = c.[0]] (disc_sup_eq).  The image chain
    [map_chain f c] has all elements equal to [f (c.[0])] since
    [c.[n] = c.[0]] (disc_chain_const).  So:
    - Upper: [f (c.[n]) = f (c.[0]) ⊑ f (c.[0])] by [le_refl].
    - Lower: [f (c.[0]) ⊑ ⊔ (map_chain f c)] by [sup_upper] at 0.
    We close with [sup_unique].
*)
Lemma disc_continuous_of_any {A : Type} {D : CPO.type}
    (f : mono_fun (Discrete A) D) : continuous f.
Proof.
  intro c.
  change (f c.[0] = ⊔ (map_chain f c)).
  apply sup_unique.
  - intro n. simpl.
    rewrite disc_chain_const.
    apply le_refl.
  - exact (sup_upper (map_chain f c) 0).
Qed.


(* ================================================================== *)
(*   §3  Bool discrete CPO                                            *)
(* ================================================================== *)
(*
    [bool] with the discrete (equality) order, registered directly on
    [bool] so that [sem_ty Bool = bool : CPO.type] in
    [PCF_Denotational.v] without any newtype wrapping.

    Structure:
      Order:  b ⊑ b'  :=  b = b'         (discrete)
      Sup:    ⊔ c     :=  c.[0]           (constant chains)

    [bool] is NOT a [PointedCPO]: [true] and [false] are incomparable,
    so neither is a least element.  Use [option bool] via [Lift.v] for
    a pointed variant.
*)

Section BoolOrder.

Definition bool_le (b1 b2 : bool) : Prop := b1 = b2.

Lemma bool_le_refl (b : bool) : bool_le b b.
Proof. 
  reflexivity. 
Qed.

Lemma bool_le_trans (b1 b2 b3 : bool) :
    bool_le b1 b2 -> bool_le b2 b3 -> bool_le b1 b3.
Proof. 
  intros ->; tauto. 
Qed.

Lemma bool_le_antisym (b1 b2 : bool) :
    bool_le b1 b2 -> bool_le b2 b1 -> b1 = b2.
Proof. 
  intros H _; exact H. 
Qed.

End BoolOrder.

HB.instance Definition bool_HasLe :=
  HasLe.Build bool bool_le.

HB.instance Definition bool_IsPreorder :=
  IsPreorder.Build bool bool_le_refl bool_le_trans.

HB.instance Definition bool_IsPartialOrder :=
  IsPartialOrder.Build bool bool_le_antisym.

Section BoolSup.

(*
    Every chain in the discrete bool CPO is constant.
    Same argument as [disc_chain_const]: [ch_mono c 0 n] gives
    [c.[0] = c.[n]] (by [bool_le = bool equality]), then symmetry.
*)
Lemma bool_chain_const (c : chain bool) (n : nat) : c.[n] = c.[0].
Proof.
  symmetry.
  exact (ch_mono c 0 n (PeanoNat.Nat.le_0_l n)).
Qed.

Definition bool_sup (c : chain bool) : bool := c.[0].

Lemma bool_sup_upper (c : chain bool) (n : nat) : c.[n] ⊑ bool_sup c.
Proof.
  unfold bool_sup.
  exact (bool_chain_const c n).
Qed.

Lemma bool_sup_least (c : chain bool) (x : bool)
    (Hub : forall n, c.[n] ⊑ x) : bool_sup c ⊑ x.
Proof.
  unfold bool_sup.
  exact (Hub 0).
Qed.

End BoolSup.

HB.instance Definition bool_HasSup :=
  HasSup.Build bool bool_sup.

HB.instance Definition bool_IsCPO :=
  IsCPO.Build bool bool_sup_upper bool_sup_least.

(*  Computation rule: [⊔ c = c.[0]] in [bool]. *)
Lemma bool_sup_eq (c : chain bool) : ⊔ c = c.[0].
Proof. reflexivity. Qed.

(*
    Every monotone function out of [bool] is Scott-continuous.
    Proof identical to [disc_continuous_of_any] — constant chains.
*)
Lemma bool_continuous_of_any {D : CPO.type} (f : mono_fun bool D) :
    continuous f.
Proof.
  intro c.
  rewrite bool_sup_eq.
  apply sup_unique.
  - intro n. simpl.
    rewrite bool_chain_const.
    apply le_refl.
  - exact (sup_upper (map_chain f c) 0).
Qed.