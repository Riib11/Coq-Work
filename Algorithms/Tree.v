Require Import ZArith Int.
Open Local Scope Z_scope.

Inductive Tree : Set :=
| empty : Tree
| node : Z -> Tree -> Tree -> Tree.

Definition left (t : Tree) :=
  match t with
  | empty => empty
  | node x l r => l
  end.

Definition right (t : Tree) :=
  match t with
  | empty => empty
  | node x l r => r
  end.

Inductive In (x : Z) : Tree -> Prop :=
| in_left : forall l r y, In x l -> In x (node y l r)
| in_right : forall l r y, In x r -> In x (node y l r)
| in_root : forall l r, In x (node x l r).

Definition is_empty (t : Tree) : bool :=
  match t with
  | empty => true
  | _ => false
  end.

Lemma is_empty_correct : forall s, (is_empty s) = true <-> forall x, ~ (In x s).
Proof.
Admitted.

Fixpoint mem (x : Z) (t : Tree) : bool :=
  match t with
  | empty => false
  | node y l r => match Z.compare x y with
    | Lt => mem x l
    | Eq => true
    | Gt => mem x r
    end
  end.

Fixpoint nat_max (m n : nat) : nat :=
  match (m,n) with
  | (O,x) => x
  | (x,O) => x
  | (S m',S n') => S (nat_max m' n')
  end.

Fixpoint height (t : Tree) : nat :=
  match t with
  | empty => O
  | node x l r => 1 + nat_max (height l) (height r)
  end.

Fixpoint cardinality (t : Tree) : nat :=
  match t with
  | empty => O
  | node x l r => 1 + cardinality l + cardinality r
  end.

Inductive BSTree : Tree -> Prop :=
  | bst_empty : BSTree empty
  | bst_node :
      forall l x r,
      BSTree l ->
      BSTree r ->
      (forall y, In y l -> y < x) ->
      (forall y, In y r -> x < y) ->
      BSTree (node x l r).

Lemma bst_left : forall t, BSTree t -> BSTree (left t).
Proof.
  intros.
  destruct H.
  simpl.
  exact bst_empty.
  simpl.
  exact H.
Qed.

Lemma bst_right : forall t, BSTree t -> BSTree (right t).
Proof.
  intros.
  destruct H.
    simpl.
    exact bst_empty.
    simpl.
    exact H0.
Qed.

Inductive AVLTree : Tree -> Prop :=
  | avl_empty : AVLTree empty
  | avl_node :
      forall l r x,
      AVLTree l ->
      AVLTree r ->
      (forall y, In y l -> y < x) ->
      (forall y, In y r -> x < y) ->
      (height l = height r \/
       height l = S(height r) \/
       S(height l) = height r) ->
      AVLTree (node x l r).

Lemma avl_left : forall t, AVLTree t -> AVLTree (left t).
Proof.
  intros.
  destruct H.
    simpl.
    exact avl_empty.
    simpl.
    exact H.
Qed.

Lemma avl_right : forall t, AVLTree t -> AVLTree (right t).
Proof.
  intros.
  destruct H.
    simpl.
    exact avl_empty.
    simpl.
    exact H0.
Qed.

Lemma nat_gt_s : forall m n, (m > n)%nat -> (S m > S n)%nat.
Proof.
Admitted.

Lemma nat_gt_1_is_O : forall m, (1 > m)%nat -> (m = O)%nat.
Proof.
Admitted.

Lemma nat_add_id : forall m, (m + 0 = m)%nat.
Proof.
Admitted.

Lemma nat_add_id_exp : forall m n, (m^n + 0 = m^n)%nat.
Proof.
  intros.
  induction m.
    simpl.
    

Lemma nat_add_id_left : forall m, (0 + m = m)%nat.
Proof.
Admitted.

Lemma nat_gt_trans : forall m n x, (m > x)%nat -> (n > m)%nat -> (n > x)%nat.
Proof.
Admitted.

Lemma nat_add_mult : forall m, (m + m = 2 * m)%nat.
Proof.
  intros.
  induction m.
    simpl.
    reflexivity.
    simpl.
    rewrite nat_add_id.
    reflexivity.
Qed.

Lemma gt_4_3 : (4 > 3)%nat. Proof. Admitted.

Lemma xxx : forall h1 h2 c1 c2 : nat, (2^h1 > c1)%nat -> (2^h2 > c2)%nat -> (2^(1 + nat_max h1 h2) > 1 + c1 + c2)%nat.
Proof.
  intros.
  simpl.
  destruct h1.
  destruct h2.
  destruct c1.
  destruct c2.
  simpl.
  auto.
  simpl.
  simpl in H.
  simpl in H0.
  apply nat_gt_s in H0.
  exact H0.
  simpl.
  simpl in H.
  simpl in H0.
  apply nat_gt_1_is_O in H0.
  rewrite H0.
  simpl.
  rewrite nat_add_id.
  apply nat_gt_s in H.
  exact H.
  simpl.
  simpl in H.
  apply nat_gt_1_is_O in H.
  rewrite H.
  rewrite nat_add_id_left.
  rewrite nat_add_id.
  induction h2.
    simpl.
    simpl in H0.
    apply nat_gt_s in H0.
    pose (sc2 := S c2).
    exact (nat_gt_trans 3 4 (S c2) H0 gt_4_3).
    simpl.
    simpl in IHh2.
    rewrite nat_add_id in IHh2.
    rewrite nat_add_id.
    rewrite nat_add_mult.
    rewrite nat_add_mult.
    
(*
Lemma max_height : forall t,
AVLTree t -> (2 ^ (height t) > cardinality t)%nat.
Proof.
  intros.
  induction t.
    simpl.
    auto.
    pose (t0 := node z t1 t2).
    pose (left := avl_left t0 H).
    simpl in left.
    pose (right := avl_right t0 H).
    simpl in right.
    pose (ind_left := IHt1 left).
    pose (ind_right := IHt2 right).
*)
  