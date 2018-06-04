(* eh, i already know how to use option for the most part *)

Require Import Nat.
Require Import List.

Variable A : Type.

Fixpoint nth_error (l : list nat) (n : nat) : option nat :=
  match l with
  | nil => None
  | h::t => match eqb h n with
            | true => Some h
            | false => nth_error t (pred n)
            end
  end.

Compute (nth_error (1::2::3::4::nil) 2).