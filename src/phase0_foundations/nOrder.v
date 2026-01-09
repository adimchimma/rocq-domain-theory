(****************************************************************************)
(* Order.v - Modern Coq implementation of constructive order theory          *)
(* for domain theory (CPOs). Uses Hierarchy-Builder, SProp, primitive        *)
(* projections, and universe polymorphism.                                  *)
(****************************************************************************)

From HB Require Import structures.
(* From HB Require notation. *)

Generalizable All Variables.
Set Universe Polymorphism.
Set Primitive Projections.

(** * Preorders - Basic order structure *)

Module Order.
  Section Defs.
    Universe Type.
    Variable (U : Universe).
    
    (** Preorder: reflexive + transitive relation *)
    #[local] Notation preorder := (preorder_of U).
    
    (** Equivalence: mutual order *)
    Definition Oeq `{preorder_of U A} (x y : A) : SProp := (x ≤ y) × (y ≤ x).
    
    (** Partial order modulo equivalence *)
    Class PartialOrder (A : Type@{U}) : Prop := PartialOrder_impl {
      order_irreflexive x : Oeq x x → False;
    }.
  End Defs.
End Order.

(** * Monotonic functions *)

Module Mono.
  Import Order.
  
  Section Mono.
    Universe Type.
    Variable (U V : Universe).
    Context `{preorder_of U A, preorder_of V B}.
    
    (** Monotonic functions preserve order *)
    Record t := Mk {
      f : A → B;
      monotonic : ∀ x y, x ≤ y → f x ≤ f y;
    }.
    
    (** Pointwise order on monotonic functions *)
    Definition le_mono (f g : t) : Prop := ∀ x, f x ≤ g x.
    
    Global Instance mono_le_proper : Proper (Oeq ==> le_mono ==> le_mono) f.
    Proof. intros ? [? Heq] ? [? Hle] ? [? Hmono] Hx Hy. by apply Hmono, Hle. Qed.
  End Mono.
End Mono.

(** * Complete Partial Orders (CPOs) *)

Module CPO.
  Import Order Mono.
  
  Section CPO.
    Universe Type.
    Variable (U : Universe).
    Context `{preorder_of U A}.
    
    (** Chain: monotonic sequence indexed by nat *)
    Definition chain := Mono.t natO A.
    
    (** CPO: computable lubs of ω-chains *)
    #[local] Notation cpo := (cpo_of U).
    
    Record t := {
      lub : chain → A;
      lub_upper x c : c x ≤ lub c;
      lub_least c x : (∀ n, c n ≤ x) → lub c ≤ x;
    }.
    
    (** Continuous functions preserve lubs *)
    Definition continuous (f : Mono.t A B) : Prop :=
      ∀ c, f (lub c) = lub (f ∘ c).
    
    Record cont (A B : cpo) : Type@{U} := MkCont {
      cont_f :> Mono.t A B;
      cont_cont : continuous cont_f;
    }.
    
    (** Pointwise continuous function space *)
    Definition cont_space (A B : cpo) : cpo.
    Proof.
      refine (cpo_ind (cont A B) _ _ _).
      - exact (λ f g, ∀ x, f x ≤ g x).
      - intros f g H. split; apply H.
      - intros c x H. apply (@lub_least _ _ (cont_space A B)).
        intros. apply H, (@lub_upper _ _ (cont_space A B), c, n).
    Defined.
  End CPO.
End CPO.

(** * Basic CPO constructions *)

Module CPOConstr.
  Import Order Mono CPO.
  
  Section Constructions.
    Universe Type.
    
    (** Discrete CPO: equality as order *)
    #[local] Notation discrete := (discrete_cpo U).
    
    Program Definition Discrete `{Eq A} : cpo A := {|
      le := eq;
      lub c n := c n;  (* any chain stabilizes *)
    |}.
    Next Obligation. by rewrite (lub_least c n). Qed.
    Next Obligation. reflexivity. Qed.
    
    (** Terminal CPO *)
    Definition One : cpo unit := Discrete _.
    
    (** Products *)
    #[local] Notation product := (product_cpo U V).
    
    Definition prod_cpo `{cpo_of U A, cpo_of V B} : cpo (A * B) := {|
      le := λ '(x1,y1) '(x2,y2), (x1 ≤ x2) × (y1 ≤ y2);
      lub c := (lub (λ n, fst (c n)), lub (λ n, snd (c n)));
    |}.
    Next Obligation. split; apply lub_upper. Qed.
    Next Obligation. intros [a b] [Ha Hb]; split; [apply lub_least|]; intros; apply Ha. Qed.
    
    (** Projections *)
    Definition proj1 `{product_cpo A B} : cont A (prod_cpo A B).
    Proof. exists (λ x, (x, ⊥)); constructor; [intros ? []; apply le_1|]. Qed.
    
    (** Cartesian closed structure *)
    Definition curry `{cpo_of U A, cpo_of V B, cpo_of W C} 
               (f : cont (prod_cpo A B) C) : cont A (cont B C).
    Proof.
      (* Implementation using HB notation would be cleaner *)
      exists (λ a b, f (a, b)); constructor.
      intros ? [Ha Hb]; apply cont_cont, lub_least; intros; apply Ha.
    Defined.
  End Constructions.
End CPOConstr.

(** * Pointed CPOs and Fixed Points *)

Module Pointed.
  Import CPO.
  
  Section Pointed.
    Universe Type.
    Class pointed (D : cpo) : Type@{U} := least : D.
    
    (** Fixed point combinator *)
    Definition fixp `{pointed D} (f : cont D D) : D := 
      lub (iterate 0 least f).
    
    (** Fixed point induction *)
    Lemma fixp_ind `{pointed D} (P : D → Prop) 
                    `{admissible P} (F : D → cont D D) :
      (∀ x, P x → P (F x x)) → P (fixp F).
    Proof.
      intros HF. apply lub_least. intros n.
      induction n as [|n IH]; rewrite iterate_succ; [apply HF, least_least|].
      apply HF, IH.
    Qed.
  End Pointed.
End Pointed.

(** * Export notations and instances *)

Export Order.Oeq.
Export CPO.le.
Export Mono.le_mono.
Notation "f ≤ g" := (Mono.le_mono f g) : mono_scope.
Notation "D1 × D2" := (CPOConstr.prod_cpo D1 D2) : cpo_scope.
Notation "D1 -c> D2" := (CPO.cont_space D1 D2) : cpo_scope.

(** * Hierarchy Builder integration *)

HB.mixin Record preorder_class A le_refl le_trans := {
  Preorder_Pack := Preorder.Pack le;
  (* Add more mixins for partial orders, cpos, etc. *)
}.

HB.builder 
  Preorder.preorder_class 
  PartialOrder.partial_order_class
  CPO.cpo_class.

(** Ready for lift monad, bifunctors, and recursive domain equations *)
