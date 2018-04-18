Inductive List (a : Type) : Type :=
  | nil  : List a
  | cons : a -> List a -> List a.

Notation "[ ]" := nil.
Infix "::"  := cons (at level 60, right associativity).

Definition natnil  := nil nat.
Definition natcons := cons nat.