Require Import List.
Require Import Arith.
Require Import Sorted.
Require Import Recdef.

Function bubble (l : list nat) {measure length} : list nat :=
  match l with
  | nil      => nil
  | n::nil   => n::nil
  | n::m::l' =>
      if leb n m
        then n::( bubble (m::l') )
        else m::( bubble (n::l') )
  end.
Proof. auto. auto. Qed.

Search lt.

Function bubble (l : list nat) {measure length} : list nat :=
  match l with
  | nil => nil
  | n :: nil => n :: nil
  | n1 :: n2 :: l' => if leb n1 n2
                      then n1 :: (bubble (n2 :: l'))
                      else n2 :: (bubble (n1 :: l'))
  end.
Proof.
  auto. auto.
Qed.

Function bubble_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | n :: l' => bubble (n :: (bubble_sort l'))
  end.


  | n::nil   => n::nil
  | n::m::l' =>
      if leb n m
        then n::( bubble (m::l') )
        else m::( bubble (n::l') )
  end.