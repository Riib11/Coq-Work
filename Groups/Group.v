Variable A : Type.
Variable default : A.

Inductive List : Type :=
  | nil  : List
  | cons : A -> List -> List.

Definition head (ls : List) : A :=
  match ls with
  | nil => default
  | cons h _ => h
  end.

Definition tail (ls : List) : List :=
  match ls with
  | nil => nil
  | cons _ t => t
  end.

Fixpoint length (ls : List) : nat :=
  match ls with
  | nil => 0
  | cons _ t => 1 + length t
  end.

Inductive In (a : A) : List -> Prop :=
  | in_head : forall ls, head ls = a -> In a ls
  | in_tail : forall ls, In a (tail ls) -> In a ls.

Inductive Group : List -> (A -> A -> A) -> A -> Type :=
  group : forall ls e op,
    (In e ls /\ forall x, In x ls -> op e x = x) ->           (* identity *)
    (forall x y, In x ls -> In y ls -> In (op x y) ls) ->     (* closed *)
    (forall x, In x ls -> exists y, In y ls /\ op x y = e) -> (* inverses *)
    Group ls op e.

Definition group_order {ls op e} (g : Group ls op e) : nat := length ls.

Definition group_elem_order {ls op e}
(g : Group ls op e) (x : a) (proof_in : In x ls) : nat :=
  match x =

Lemma elem_order_leq_group_order {ls op e} (g : Group ls op e) :
forall x, In x ls -> group_elem_order x <= group_order ls.