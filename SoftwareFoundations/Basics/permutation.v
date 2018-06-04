Definition A := nat.

Fixpoint tail (l : list A) : list A :=
  match l with
  | nil      => nil
  | cons h t => t
  end.

Inductive In : A -> list A -> Prop :=
  | in_head (a:A) (l:list A) : In a (a::l)
  | in_tail (a:A) (l:list A) : In a (tail l) -> In a l.

Inductive Permutation : list A -> list A -> Prop :=
  | perm_nil   : Permutation nil nil
  | perm_skip  : forall x l l',
      Permutation l l' ->
      Permutation (cons x l) (cons x l')
  | perm_swap  : forall x y l,
      Permutation (cons x (cons y l)) (cons y (cons x l))
  | perm_trans : forall l l' l'',
      Permutation l l' -> Permutation l' l'' ->
      Permutation l l''.

Definition l1 := (cons 1 (cons 2 nil)).
Definition l2 := (cons 2 (cons 1 nil)).

Theorem perm_refl : forall l, Permutation l l.
Proof.
  intros.
  induction l.
    exact perm_nil.
    exact (perm_skip a l l IHl).
Qed.

Example simple_permutation : Permutation l1 l2.
Proof.
  refine (perm_swap _ _ _).
Qed.

Fixpoint concat (l l':list A) : list A :=
  match l with
  | nil      => l'
  | cons h t => cons h (concat t l')
  end.

Fixpoint reverse (l:list A) : list A :=
  match l with
  | nil      => nil
  | cons h t => concat (reverse t) (cons h nil)
  end.

Theorem reverse_is_permutation :
  forall (l:list A), Permutation l (reverse l).
Proof.
  intros.
  refine (perm_trans _ _ _ _ _).
    destruct l.
    