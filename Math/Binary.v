Set Implicit Arguments.

Inductive Bit : Type := | t : Bit | f : Bit.

Fixpoint flip (x : Bit) : Bit := match x with
  | t => f
  | f => t
end.

Fixpoint bin_to_nat (x : Bit) : nat := match x with
  | t => 1
  | f => 0
end.

Fixpoint bit_xor (x y : Bit) : Bit :=
  match (x,y) with
    | (t,t) => f
    | (t,f) => t
    | (f,t) => t
    | (f,f) => f
  end.

Inductive BitString : nat -> Type :=
  | nil  : BitString 0
  | cons {n : nat} (x : Bit) (bs : BitString n) : BitString (S n).

Notation "x :: xs" := (cons x xs).
Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition length {n : nat} (bs : BitString n) : nat := n.

Lemma length_0_is_nil : forall (n : nat) (bs : BitString n), n = 0 -> bs = [].
Proof.
  intros.
  inductive bs

Definition default := f.

Definition head {n : nat} (bs : BitString n) : Bit :=
  match bs with
    | [] => default
    | x :: xs => x
  end.

Definition tail {n : nat} (bs : BitString (S n)) : BitString n :=
  match bs with
    | [] => []
    | x :: xs => xs
  end.

Fixpoint app {n : nat} (b : Bit) (bs : BitString n) : BitString (S n) :=
  match bs with
    | [] => [b]
    | x :: xs => x :: app b xs
  end.

Fixpoint index {n : nat} (i : nat) (bs : BitString n) : Bit :=
  match bs with
    | [] => default
    | x :: xs => match i with
        | 0 => x
        | S n' => index n' xs
      end
  end.

Fixpoint mutate {n : nat} (i : nat) (bs : BitString n) : BitString n :=
  match bs with
    | [] => []
    | x :: xs => match i with
        | 0 => flip x :: xs
        | S n' => x :: mutate n' xs
      end
  end.

Fixpoint bs_bitshiftright {n : nat} (i : nat) (bs : BitString n) : BitString n :=
  match i with
    | 0 => bs
    | S i' => bs_bitshiftright i' ( match bs with
        | [] => []
        | x :: xs => app f xs
      end)
  end.

Fixpoint bs_xor {n : nat} (bs bs' : BitString n) : BitString n :=
  match (bs,bs') with
    | ([],[]) => []
    | (x::xs,y::ys) => bit_xor x y :: bs_xor xs ys
  end.

Fixpoint bs_to_nat {n : nat} (bs : BitString n) : nat :=
  match bs with
    | [] => 0
    | x :: xs => (bin_to_nat x) + 2 * (normal_map xs)
  end.

Fixpoint gray_encode {n : nat} (bs : BitString n) : BitString n :=
  match bs with


Fixpoint mutation_distance : {n : nat} (i : nat) (bs : BitString n) : nat :=