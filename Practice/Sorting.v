Variable A : Type.
Variable a1 a2 a3 : A.

Inductive List : Type -> Type :=
  | nil  : List A
  | cons : A -> List A -> List A.

Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "x :: xs" := (cons x xs).

Fixpoint head (l:List A) : option A :=
  match l with
  | [] => None
  | x::_ => Some x
  end.

Fixpoint bottom (l:List A) : option A :=
  match l with
  | [] => None
  | _::xs => bottom xs
  end.

Fixpoint tail (l:List A) : List A :=
  match l with
  | [] => []
  | x::xs => xs
  end.

Inductive In : A -> List A -> Prop :=
  | in_head (a:A) (l:List A) : (Some a = head l) -> In a l
  | in_tail (a:A) (l:List A) : (In a (tail l)) -> In a l.

(*Fixpoint In (a:A) (l:List A) : Prop :=
  match l with
  | [] => False
  | x::xs => a = x \/ In a xs
  end.*)

Fixpoint Permutation (l l':List A) : Prop :=
  forall a:A, In a l -> In a l'.

Fixpoint Reverse (l l':List A) : Prop :=
  match l with
  | [] => l = l'
  | x::xs => match bottom l' with
             | None   => False
             | Some b => x = b /\ (Reverse xs (tail l'))
             end
  end.

Fixpoint append (a:A) (l:List A) : List A :=
  match l with
  | [] => [a]
  | x::xs => x :: append a xs
  end.

Fixpoint reverse (l:List A) : List A :=
  match l with
  | [] => []
  | x::xs => append x (reverse xs)
  end.

Theorem reverse_correct : forall (l:List A), Reverse l (reverse l).
Proof.
  intros.
  unfold Reverse.
  induction l.