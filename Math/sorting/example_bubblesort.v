Require Import List.
Require Import Arith.
Require Import Sorted.
Require Import Recdef.

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

Check Sorted.

Check (Sorted le).

Print Sorted.

Print HdRel.

(* 
Sorted_cons:
  forall (a : A) (l : list A),
  Sorted R l -> HdRel R a l -> Sorted R (a :: l)

HdRel_nil : HdRel R a nil
HdRel_cons : forall (b : A) (l : list A), R a b -> HdRel R a (b :: l)
*)

Check bubble_terminate.
Check iter.

Theorem bubble_sort_correct : forall l, Sorted le (bubble_sort l).
Proof.
  intros.
  induction l.
    simpl. apply Sorted_nil.
    simpl. destruct l.
      simpl. unfold bubble.
      unfold bubble_terminate.

Eval compute in bubble      (1 :: 2 :: 0 :: 3 :: 1 :: nil).
Eval compute in bubble_sort (1 :: 2 :: 0 :: 3 :: 1 :: nil).
Eval compute in bubble_sort (1 :: 2 :: 10 :: 3 :: 6 :: nil).