Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

Variable X : Type.

Notation "[ ]" := nil.
Notation "h :: t" := (cons h t) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "xs ++ ys" := (app xs ys).

Theorem app_nil_r : forall l : list X, l ++ [] = l.
Proof.
  intros.
  induction l.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall l m n : list X, l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l. destruct m. destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_length : forall l l' : list X, length l + length l' = length (l ++ l').
Proof.
  intros.
  induction l. destruct l'.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Fixpoint rev (l : list X) : list X :=
  match l with
  | []   => []
  | h::t => rev t ++ [h]
  end.

Theorem rev_app_distr : forall l l' : list X, rev (l ++ l') = rev l' ++ rev l.
Proof.
  intros.
  induction l. destruct l'.
    simpl. reflexivity.
    simpl. rewrite app_nil_r. reflexivity.
    simpl. rewrite IHl. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_app : forall x l, rev l ++ [x] = rev (x::l).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Theorem rev_rev_app : forall x l, rev (rev (x::l)) = x :: rev (rev l).
Admitted.

Theorem rev_involutive : forall l : list X, rev (rev l) = l.
Proof.
  intros.
  induction l.
    simpl. reflexivity.
    rewrite rev_rev_app. rewrite IHl. reflexivity.
Qed.

