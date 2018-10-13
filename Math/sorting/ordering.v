Add LoadPath "/Users/Henry/Documents/Drive/Coq/Math/sorting".
Load natlist.

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
  | []   => true
  | m::_ => leb n m
  end.

Inductive sorted : natlist -> Prop :=
  | sorted_nil  : sorted []
  | sorted_cons : forall (n : nat) (l : natlist),
      sorted l -> can_head n l = true -> sorted (cons n l).

Example sorted_singleton : forall n, sorted (cons n nil).
Proof.
  intros.
  refine (sorted_cons _ _ _ _ ).
  apply sorted_nil.
  exact (eq_refl : can_head n [] = true).
Qed.

Ltac red_sorted_cons := (refine (sorted_cons _ _ _ _)).

(* Example example1 : sorted (cons 1 (cons 2 (cons 3 nil))). *)
Example sorted_example1 : sorted [1;2;3].
Proof.
  red_sorted_cons. red_sorted_cons. red_sorted_cons.
  apply sorted_nil.
  apply eq_refl. apply eq_refl. apply eq_refl.
Qed.

Example sorted_example2 : ~ sorted [2;1].
Proof.
  unfold not.
  intros.
  inversion H.
  simpl in H3.
  discriminate.
Qed.

Example sorted_example3 : forall n, sorted [n;S n].
Proof.
  intros. red_sorted_cons. red_sorted_cons.
  apply sorted_nil.
  simpl. reflexivity.
  simpl. cut (leb n (S n) = true). intros. exact H.
  induction n.
    simpl. reflexivity.
    simpl. apply IHn.
Qed.