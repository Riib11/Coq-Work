Require Import Arith_base.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.

Inductive vector A : nat -> Type :=
  | nil : vector A 0
  | cons : forall (h:A) (n:nat), vector A n -> vector A (S n).



