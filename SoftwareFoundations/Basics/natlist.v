Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Notation "[ ]" := nil.
Notation "h :: t" := (cons h t)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O   => []
  | S c => n :: (repeat n c)
  end.

Fixpoint length xs : nat :=
  match xs with
  | []    => O
  | h::t => S (length t)
  end.

Fixpoint concat xs ys : natlist :=
  match xs with
  | []   => ys
  | h::t => h :: (concat t ys)
  end.

Notation "xs ++ ys" := (concat xs ys)
                       (at level 60, right associativity).

Axiom N0 : nat.
Axiom L0 : natlist.

Definition head xs : nat :=
  match xs with
  | []   => N0
  | h::_ => h
  end.

Definition tail xs : natlist :=
  match xs with
  | []   => []
  | _::t => t
  end.

Fixpoint nonZeros xs : natlist :=
  match xs with
  | []   => []
  | h::t => match h with
            | O   => nonZeros t
            | S _ => h :: nonZeros t
            end
  end.

Fixpoint notb b : bool :=
  match b with | true => false | false => true end.

Fixpoint eqb m n : bool :=
  match (m,n) with
  | (O,O) => true
  | (S m,S n) => eqb m n
  | _ => false
  end.

Fixpoint gtb m n : bool :=
  match (m,n) with
  | (O,_) => false
  | (_,O) => true
  | (S m,S n) => gtb m n
  end.

Fixpoint isEven n : bool :=
  match n with
  | O    => true
  | S n' => notb (isEven n')
  end.

Fixpoint oddMembers xs : natlist :=
  match xs with
  | []   => []
  | h::t => if isEven h
            then oddMembers t
            else h :: oddMembers t
  end.

Definition countOddMembers xs : nat :=
  length (oddMembers xs).

Fixpoint alternate xs ys : natlist :=
  match (xs,ys) with
  | ([],ys) => ys
  | (xs,[]) => xs
  | (x::xs,y::ys) => x :: y :: (alternate xs ys)
  end.

Fixpoint count n xs : nat :=
  match xs with
  | []   => O
  | h::t => if eqb n h
            then 1 + count n t
            else count n t
  end.

Definition bag := natlist.

Definition sum : bag -> bag -> bag := concat.

Definition add : nat -> bag -> bag := cons.

Definition member : nat -> bag -> bool := fun n b => gtb (count n b) 0.

Theorem nil_concat : forall l, [] ++ l = l.
Proof.
  simpl. reflexivity.
Qed.

Theorem nil_concat_right : forall l, l ++ [] = l.
Proof.
  induction l as [| x l'].
    simpl. reflexivity.
    simpl. rewrite IHl'. reflexivity.
Qed.

Theorem tail_length_pred : forall l, pred (length l) = length (tail l).
Proof.
  intros l.
  destruct l as [| x l'].
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Fixpoint reverse l : natlist :=
  match l with
  | []   => []
  | h::t => reverse t ++ [h]
  end.

Theorem concat_length : forall l l', length (l ++ l') = length l + length l'.
Proof.
  intros.
  induction l. destruct l'.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem add_1_is_S : forall n, S n = n + 1.
Proof.
  intro n. simpl.
  induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem reverse_preserves_length : forall l, length l = length (reverse l).
Proof.
  intros l.
  induction l.
    simpl. reflexivity.
    simpl. rewrite IHl.
    rewrite concat_length.
    simpl. rewrite add_1_is_S. reflexivity.
Qed.

Theorem concat_associative : forall a b c, (a ++ b) ++ c = a ++ b ++ c.
Proof.
  intros.
  induction a. destruct b. destruct c.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHa. reflexivity.
Qed.

Theorem reverse_distributes_concat :
  forall l l', reverse (l ++ l') = reverse l' ++ reverse l.
Proof.
  intros.
  induction l. destruct l'.
    simpl. reflexivity.
    simpl. rewrite nil_concat_right. reflexivity.
    simpl. rewrite IHl. rewrite concat_associative. reflexivity.
Qed.

Theorem reverse_append : forall l n, reverse (l ++ [n]) = n :: reverse l.
Proof.
  intros.
  induction l.
    simpl. reflexivity.
    simpl. rewrite IHl. simpl. reflexivity.
Qed.

Theorem reverse_prepend : forall l n, reverse (n :: l) = reverse l ++ [n].
Proof.
  intros.
  destruct l as [| h t].
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem reverse_involutive : forall l, reverse (reverse l) = l.
Proof.
  intros.
  induction l.
    simpl. reflexivity.
    simpl. rewrite reverse_append. rewrite IHl. reflexivity.
Qed.

Fixpoint andb b b' : bool :=
  match (b,b') with
  | (true,true) => true
  | _ => false
  end.

Fixpoint eqb_natlist l l' : bool :=
  match l,l' with
  | [],[] => true
  | h::t,[] => false
  | [],h::t => false
  | h::t,h'::t' => andb (eqb h h') (eqb_natlist t t')
  end.

Fixpoint leb m n : bool :=
  match m,n with
  | _,O => false
  | O,S _ => true
  | S m, S n => leb m n
  end.

Theorem count_member_nonzero :
  forall s, leb 0 (count 1 (1::s)) = true.
Proof.
  intros.
  simpl. reflexivity.
Qed.

Theorem concat_count : forall x l l', count x l + count x l' = count x (l ++ l').
  intros.
  induction l. destruct l'.
    simpl. reflexivity.
    simpl. reflexivity. simpl.
    case (eqb x n).
      simpl. rewrite IHl. reflexivity.
      simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_eq_natlist : forall l l', l = l' -> reverse l = reverse l'.
Proof.
  intros.
  induction l. destruct l'.
    simpl. reflexivity.
    simpl. rewrite <- reverse_prepend.
    rewrite <- H. simpl. reflexivity.
    rewrite H. reflexivity.
Qed.

