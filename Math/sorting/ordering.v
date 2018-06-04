Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Axiom nat_default : nat.

Fixpoint head (l : natlist) :=
  match l with
  | nil => nat_default
  | cons h t => h
  end.

Fixpoint eqb (n m : nat) :=
  match n,m with
  | O,O => true
  | O,_ => false
  | _,O => false
  | S n,S m => eqb n m
  end.

Fixpoint leb (n m : nat) :=
  match n,m with
  | O,_ => true
  | _,O => false
  | S n,S m => leb n m
  end.

Definition can_head (n : nat) (l : natlist) :=
  match l with
  | nil => true
  | cons m _ => leb n m
  end.

Inductive sorted : natlist -> Prop :=
  | sorted_nil  : sorted nil
  | sorted_cons : forall (n : nat) (l : natlist),
      sorted l -> can_head n l = true -> sorted (cons n l).

Example singleton_is_sorted : forall n, sorted (cons n nil).
Proof.
  intros.
  refine (sorted_cons _ _ _ _ ).
  apply sorted_nil.
  exact (eq_refl : can_head n nil = true).
Qed.

