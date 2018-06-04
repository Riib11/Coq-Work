Inductive Val : Type :=
  | infinity : Val
  | finite   : nat -> Val.

Axiom V0 : Val.

Fixpoint Leq_p (a b:nat) : Prop :=
  match (a,b) with
  | (O,O) => True
  | (O,_) => True
  | (_,O) => False
  | (S a',S b') => Leq_p a' b'
  end.

Fixpoint Comp (a b:Val) : Prop :=
  match (a,b) with
  | (finite a, finite b) => Leq_p a b
  | (finite _, infinity) => True
  | (infinity, finite b) => False
  | (infinity, infinity) => True
  end.

Fixpoint getVal h : Heap v -> Val := v.

Inductive Heap : Val -> Type :=
  | stub : Heap infinity
  | node (v:Val) (l r:Heap) : Comp (getVal l) v -> Comp (getVal r) v -> Heap.


Fixpoint leftChild h : Val :=
  match h with
  | stub => HV0
  | node l v _ _ _ => l
  end.

Fixpoint 

Lemma child_leq : forall H, 