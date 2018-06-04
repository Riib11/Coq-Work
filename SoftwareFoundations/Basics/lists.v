Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: xs" := (cons x xs)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint concat (xs : natlist) (ys : natlist) :=
  match ys with
  | []  => xs
  | ys'  =>
      match xs with
      | []    => ys'
      | [x]   => x :: ys'
      | x::xs' => x :: concat xs' ys'
      end
  end.
Notation "xs ++ ys" := (concat xs ys).

Fixpoint rev (xs : natlist) :=
  match xs with
  | [] => xs
  | x::xs' => rev xs' ++ [x]
  end.

Inductive In : 

Fixpoint index (xs : natlist) (t : nat) :=
  match xs with
  | [] => 

Theorem app_nil_r : forall l : natlist, l ++ [] = l.
Proof.
  intro l.
  simpl.