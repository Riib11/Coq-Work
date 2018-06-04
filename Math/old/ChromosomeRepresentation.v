Inductive Binary : Type := | t : Binary | f : Binary.

Inductive BinaryString : Type :=
  | nil : BinaryString
  | cons : Binary -> BinaryString -> BinaryString.

Fixpoint length (bs : BinaryString) :=
  match bs with
    | nil => 0
    | cons x xs => S (length xs)
  end.

Definition mutate
  (i : nat) (bounded : i < length bs) (bs : BinaryString) :
  BinaryString :=
  
  