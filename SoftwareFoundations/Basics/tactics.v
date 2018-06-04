Require Import Setoid.

Fixpoint beq_nat (n m : nat) : bool :=
  match n,m with
  | O,O => true
  | O,_ => false
  | _,O => false
  | S n,S m => beq_nat n m
  end.

Theorem beq_nat_eq : forall n m : nat, n = m <-> beq_nat n m = true.
Admitted.

Check eq_sym.

Theorem beq_nat_S : forall n m : nat, beq_nat n m = beq_nat (S n) (S m).
Proof.
  intros.
  induction n. induction m.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem beq_nat_sym : forall n m : nat, beq_nat n m = beq_nat m n.
Proof.
Admitted.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat p n = true.
Proof.
  intros.
  destruct m. destruct n. destruct p.
    simpl. reflexivity.
    apply beq_nat_eq in H0.
    rewrite H0. simpl. rewrite <- beq_nat_eq. reflexivity.
    rewrite beq_nat_sym in H0. rewrite <- beq_nat_eq in H0.
      rewrite beq_nat_sym. rewrite H0. exact H.
    rewrite <- beq_nat_eq in H. rewrite H. rewrite beq_nat_sym. exact H0.
Qed.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | nil, _ => nil
  | _, nil => nil
  | cons x tx, cons y ty => cons (x,y) (combine tx ty)
  end.

Fixpoint split_fst {X Y : Type} (l : list (X*Y)) : list X :=
  match l with
  | nil => nil
  | cons (x,y) t => cons x (split_fst t)
  end.

Fixpoint split_snd {X Y : Type} (l : list (X*Y)) : list Y :=
  match l with
  | nil => nil
  | cons (x,y) t => cons y (split_snd t)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  (split_fst l, split_snd l).

Theorem split_cons : forall X Y (a : (X*Y)) (l : list (X*Y)),
  split (cons a l) = (cons (fst a) (fst (split l)), cons (snd a) (snd (split l))).
Admitted.

Theorem split_cons_1 : forall (X Y : Type) (x:X) (y:Y) l xs ys,
  split l = (cons x xs, cons y ys) -> l = cons (x,y) (combine xs ys).
Admitted.

Theorem split_nil : forall X Y (l : list (X*Y)), split l = (nil, nil) -> l = nil.
Admitted.

Theorem split_rnil : forall X Y (l : list (X*Y)) (l' : list X), split l = (l',nil) -> l = nil.
Admitted.

Theorem split_lnil : forall X Y (l : list (X*Y)) (l' : list Y), split l = (nil,l') -> l = nil.
Admitted.

Theorem eq_sym_again : forall A (x y : A), x = y -> y = x.
Proof. exact eq_sym. Qed.

Theorem combine_split : forall X Y (l : list (X*Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros.
  induction l1. induction l2.
    apply split_nil in H.
    rewrite H. simpl. reflexivity.
    simpl. pose (H2 := split_lnil X Y l ((a::l2)%list) H).
    pose (H3 := eq_sym H2).
    exact H3.
    pose (H1 := split_cons ).

Lemma split_cons_combine : forall (X Y : Type) (a : X) (l : list (X*Y)) (l1 : list X) (l2 : list Y), split l = (cons a l1, l2) -> combine (cons a l1) l2 = l.
Proof.
  intros.
  induction l1. induction l2.
    simpl. apply split_rnil in H. apply eq_sym in H. exact H.
    simpl. apply split_cons_1 in H. rewrite H. simpl. reflexivity.
Admitted.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) :=
  match l with
  | nil => nil
  | cons h t => if test h then cons h (filter test t) else filter test t
  end.

Notation "h :: t " := (cons h t) (at level 60, right associativity).

Theorem list_head_eq : forall (A:Type) (x y : A) (xs ys : list A), x::xs = y::ys -> x = y.
Admitted.

Theorem list_head_filter : forall (A:Type) (test:A->bool) (x:A) (l lf:list A),
  filter test l = x :: lf -> test x = true.
Proof.
  intros.
  induction l. induction lf.
    simpl in H. discriminate.
    simpl in H. discriminate.
    simpl in H. destruct (test a).
    pose (H1 := list_head_eq A a x (filter test l) lf H).
    rewrite <- H1 in IHl.
    pose (H2 := H).
    rewrite <- H1 in H2.
Admitted.