Inductive Nat : Type :=
  | O : Nat
  | S : Nat -> Nat.

Inductive NatList : Type :=
  | nil : NatList
  | cons : Nat -> NatList -> NatList.

Notation "[ ]" := nil.
Notation "[ x ]" := (cons x []).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z []) ..)).
Notation "x :: xs" := (cons x xs).

Fixpoint head (l:NatList) : option Nat :=
  match l with
  | [] => None
  | x::_ => Some x
  end.

Fixpoint bottom (l:NatList) : option Nat :=
  match l with
  | [] => None
  | x::[] => Some x
  | _::xs => bottom xs
  end.

Fixpoint tail (l:NatList) : NatList :=
  match l with
  | [] => []
  | x::xs => xs
  end.

Inductive In (a:Nat) (l:NatList) : Prop :=
  | in_head : (Some a = head l) -> In a l
  | in_tail : (In a (tail l)) -> In a l.

(*Fixpoint In (a:A) (l:NatList) : Prop :=
  match l with
  | [] => False
  | x::xs => a = x \/ In a xs
  end.*)

Fixpoint Permutation (l l':NatList) : Prop :=
  forall a:Nat, In a l -> In a l'.

Fixpoint Reverse (l l':NatList) : Prop :=
  match l with
  | [] => l = l'
  | x::xs => match bottom l' with
             | None   => False
             | Some b => x = b \/ (Reverse xs (tail l'))
             end
  end.

Fixpoint append (a:Nat) (l:NatList) : NatList :=
  match l with
  | [] => [a]
  | x::xs => x :: append a xs
  end.

Fixpoint reverse (l:NatList) : NatList :=
  match l with
  | [] => []
  | x::xs => append x (reverse xs)
  end.

Lemma reverse_correct_helper :
  forall (x : Nat) (l:NatList),
  Reverse (x::l) (reverse (x::l))
  -> Reverse l (reverse l).
Proof.
  intros.
  induction l.
    simpl. reflexivity.
    rewrite IHl.


Theorem reverse_correct : forall (l:NatList), Reverse l (reverse l).
Proof.
  intros.
  induction l.
    (* base case *)
    simpl.
    reflexivity.
    (* induction *)
    destruct l.
      (* nil *)
      simpl.
      constructor.
      reflexivity.
      (* cons *)
      simpl.