(** Algebraic and order-theoretic hierarchies

    This module uses Hierarchy-Builder to define algebraic structures
    and order-theoretic hierarchies for domain theory.
    
    This demonstrates how HB can be used to organize mathematical structures
    with automatic instance generation and inheritance.
    
    This module is part of the rocq-domain-theory project.
*)

From HB Require Import structures.

(** * Algebraic Hierarchy *)

(** ** Magmas: Types with a binary operation *)
HB.mixin Record hasOp (T : Type) := { op : T -> T -> T }.
HB.structure Definition Magma := { T of hasOp T }.

(** ** Semigroups: Magmas with associativity *)
HB.mixin Record isAssociative (T : Type) of hasOp T := {
  op_assoc : forall x y z : T, op x (op y z) = op (op x y) z
}.
HB.structure Definition Semigroup := { T of hasOp T & isAssociative T }.

(** ** Monoids: Semigroups with an identity element *)
HB.mixin Record hasIdentity (T : Type) of hasOp T := {
  identity : T ;
  identity_left : forall x : T, op identity x = x ;
  identity_right : forall x : T, op x identity = x
}.
HB.structure Definition Monoid := { T of hasOp T & isAssociative T & hasIdentity T }.

(** ** Commutative Monoids *)
HB.mixin Record isCommutative (T : Type) of hasOp T := {
  op_comm : forall x y : T, op x y = op y x
}.
HB.structure Definition ComMonoid := 
  { T of hasOp T & isAssociative T & hasIdentity T & isCommutative T }.

(** * Order-Theoretic Hierarchy *)

(** ** Preorders: Types with a reflexive, transitive relation *)
HB.mixin Record hasPreorder (T : Type) := {
  le_op : T -> T -> Prop ;
  le_refl_ax : forall x : T, le_op x x ;
  le_trans_ax : forall x y z : T, le_op x y -> le_op y z -> le_op x z ;
}.
HB.structure Definition PreorderType := { T of hasPreorder T }.

(** ** Partial Orders: Preorders with antisymmetry *)
HB.mixin Record isAntisymmetric (T : Type) of hasPreorder T := {
  le_antisym : forall x y : T, le_op x y -> le_op y x -> x = y
}.
HB.structure Definition PartialOrder := { T of hasPreorder T & isAntisymmetric T }.

(** ** Monotone Functions between preorders *)
HB.mixin Record isMonotone (D E : PreorderType.type) (f : D -> E) := {
  mono_preserves : forall x y : D, 
    @le_op D x y -> @le_op E (f x) (f y)
}.
HB.structure Definition MonoFun (D E : PreorderType.type) := 
  { f of isMonotone D E f }.

(** ** ω-chains in a preorder *)
(** A chain is a sequence with monotonicity *)
HB.mixin Record isChain (T : PreorderType.type) (c : nat -> T) := {
  chain_mono : forall m n : nat, m <= n -> @le_op T (c m) (c n)
}.
HB.structure Definition Chain (T : PreorderType.type) := { c of isChain T c }.

(** ** CPOs: Preorders with lubs of ω-chains *)
HB.mixin Record hasCPO (T : Type) of hasPreorder T := {
  lub : (nat -> T) -> T ;
  (* Simplified: In practice, lub should only be defined for chains *)
  lub_upper_ax : forall (c : nat -> T), 
    (forall m n, m <= n -> le_op (c m) (c n)) ->
    forall n, le_op (c n) (lub c) ;
  lub_least_ax : forall (c : nat -> T) (x : T), 
    (forall m n, m <= n -> le_op (c m) (c n)) ->
    (forall n, le_op (c n) x) -> 
    le_op (lub c) x
}.
HB.structure Definition CPOType := { T of hasPreorder T & hasCPO T }.

(** ** Pointed CPOs: CPOs with a least element *)
HB.mixin Record hasBottom (T : Type) of hasPreorder T & hasCPO T := {
  bottom : T ;
  bottom_least : forall x : T, le_op bottom x
}.
HB.structure Definition PointedCPOType := { T of hasCPO T & hasBottom T }.

(** * Inspection commands *)
HB.about Magma.
HB.about Semigroup.
HB.about Monoid.
HB.about PreorderType.
HB.about CPOType.
HB.about PointedCPOType.
