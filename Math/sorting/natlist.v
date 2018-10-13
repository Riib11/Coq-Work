Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "h :: t" := (cons h t) (at level 60, right associativity).

Axiom nat_default : nat.

Definition head (l : natlist) :=
  match l with
  | []   => nat_default
  | h::t => h
  end.

Definition head_safe (l : natlist) (safety : ~ l = nil) : nat.
  destruct l.
  unfold not in safety.
  case (safety (eq_refl : [] = [])).
  exact n.
Defined.

Lemma not_nil_example1 : ~ [1;2] = nil.
Proof. intros. unfold not. intros. inversion H. Qed.

Example head_safe_example1 : head_safe [1;2] not_nil_example1 = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint append (n : nat) (l : natlist) : natlist :=
  match l with
  | [] => [n]
  | h::t => h :: (append n t)
  end.

Fixpoint concat (xs ys : natlist) : natlist :=
  match ys with
  | [] => ys
  | h::t => concat (append h xs) t
  end.

Notation "xs ++ ys" := (concat xs ys) (at level 60, right associativity).

Fixpoint length (l : natlist) :=
  match l with
  | [] => 0
  | _::t => 1 + length t
  end.