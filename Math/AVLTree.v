Require Import
  FSetInterface
  FMapInterface
  FMapList
  ZArith
  Int.

Import Z_as_Int.

Set Implicit Arguments.

(* notation of 2-tuples *)
Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

(* integers *)
Definition int := Z.

(* keys are integers *)
Definition key := int.

(* avltree inductive type *)
Inductive avltree :=
  | Leaf : avltree
  | Node : key -> avltree -> avltree -> nat -> avltree.
    (* key, left, right, height *)

Definition height (t:avltree) : nat :=
  match t with
    | Leaf => 0
    | Node _ _ _ h => h
  end.

Fixpoint cardinal (t:avltree) : nat :=
  match t with
    | Leaf => 0
    | Node _ l r _ => S (cardinal l + cardinal r)
  end.

Fixpoint nat_max (m n:nat) : nat :=
  match m ?= n with
    | Lt => n
    | Eq => n
    | Gt => m
  end.

Fixpoint nat_eq (m n:nat) : bool :=
  match m ?= n with
    | Eq => true
    | _  => false
  end.

Definition create k l r :=
  Node k l r (nat_max (height l) (height r) + 1).

Definition assert_false := create.

Fixpoint balance k l r : avltree :=
  let hl := height l in
  let hr := height r in
  if nat_eq hl (hr+2) then
      match l with
      | Leaf => assert_false k l r
      | Node lk ll lr _ =>
        if nat_eq (height ll) (height lr) then
          create lk ll (create k lr r)
          else
            match lr with
            | Leaf => assert_false k l r
            | Node lrk lrl lrr _ =>
                create lrk (create lk ll lrl) (create k lrr r)
            end
      end
  else
    if nat_eq hr (hl+2) then
      match r with
        | Leaf => assert_false k l r
        | Node rk rl rr _ =>
          if nat_eq (height rr) (height rl) then
            create rk (create k l rl) rr
          else
            match rl with
              | Leaf => assert_false k l r
              | Node rlk rll rlr _ =>
                  create rlk (create k l rll) (create rk rlr rr)
            end
      end
  else
    create k l r.

Fixpoint remove_min (k:key) (l r:avltree) : avltree * key :=
  match l with
    | Leaf => (r,k)
    | Node lk ll lr lh =>
        let (l',m) := remove_min lk ll lr in
        (balance k l' r, m)
  end.

Fixpoint merge (t s:avltree) : avltree :=
  match t,s with
    | Leaf, _ => s
    | _, Leaf => t
    | _, Node sk sl sr sh =>
        match remove_min sk sl sr with
          (s',k) => balance k sl s'
        end
  end.

Fixpoint insert (k:key) (t:avltree) : avltree :=
  match t with
    | Leaf => Node k Leaf Leaf 1
    | Node k' l r h =>
        match Z.compare k k' with
          | Lt => balance k' (insert k l) r
          | Eq => Node k' l r h
          | Gt => balance k' l (insert k r)
        end
  end.

Fixpoint remove (k:key) (t:avltree) : avltree :=
  match t with
    | Leaf => Leaf
    | Node k' l r h =>
        match Z.compare k k' with
          | Lt => balance k (remove k' l) r
          | Eq => merge l r
          | Gt => balance k l (remove k' r)
        end
  end.

(* want to show that given a certain type of tree,
the resulting tree after a deletion will be 1 less height *)

Theorem test : forall (t : avltree) (m n : nat),
  m > n -> height t > m -> height t > n.
Proof.
  intros.
  apply (gt_trans (height t0) m n ).
  exact H0.
  exact H.
Qed.

Theorem remove_height : forall (t : avltree) (k : key),
  height t >= height (remove k t).
Proof.
  intros.
  