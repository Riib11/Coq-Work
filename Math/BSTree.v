Require Import ZArith Int.
Open Local Scope Z_scope.

Set Implicit Arguments.

Inductive Key : Set :=
| val : Z -> Key
| nil : Key.

Definition Nat := nat.

Inductive Ordered : Key -> Key -> Prop :=
  | ord_both  (l r : Z) : (l ?= r) = Lt -> Ordered (val l) (val r)
  | ord_left  (l   : Z) : Ordered (val l) nil
  | ord_right (  r : Z) : Ordered nil     (val r)
  | ord_nil             : Ordered nil     nil.

Inductive BSTree : Key -> Type :=
| leaf : BSTree nil
| branch
    {lk k rk : Key}
    (l : BSTree lk)
    (r : BSTree rk)
    (l_ord : Ordered lk k)
    (r_ord : Ordered k rk)
    : BSTree k.

Fixpoint nat_max (m n : Nat) : Nat :=
  match (m,n) with
  | (O,_) => O
  | (_,O) => O
  | (S m',S n') => S (nat_max m' n')
  end.

Fixpoint height {k : Key} (t : BSTree k) : Nat :=
  match t with
  | leaf => O
  | branch k l r l_ord r_ord => S (nat_max (height l) (height r))
  end.