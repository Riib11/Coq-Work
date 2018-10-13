Add LoadPath "/Users/Henry/Documents/Drive/Coq/Math/sorting".
Load ordering.

Fixpoint removelast (l : natlist) :=
  match l with
  | []    => []
  | h::[] => []
  | h::t  => h :: removelast t
  end.

Fixpoint last (l : natlist) (default : nat) :=
  match l with
  | []    => default
  | h::[] => h
  | h::t  => last t default
  end.

Fixpoint bubble_sort' (l : natlist) (n : nat) (time : nat) : natlist :=
  match time with
  | 0    => l
  | S t' =>
      match l with
      | nil => nil
      | cons n' nil =>
          match (leb n n') with
          | true  => cons n  (cons n' nil)
          | false => cons n' (cons n nil)
          end
      | cons n' (cons n'' _ as l') =>
          match (leb n n') with
          | true  => let l'' :=
              bubble_sort' l' n' t' in
              (bubble_sort' (removelast l'') n  t') ++ ((last l'' 0) :: nil)
          | false => let l'' :=
              bubble_sort' l' n  t' in
              (bubble_sort' (removelast l'') n' t') ++ ((last l'' 0) :: nil)
          end
      end
  end.

Fixpoint bubble_sort (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h::[] => h::[]
  | h::t  => bubble_sort' t h (length t)
  end.

Compute (bubble_sort [2;1]).

Check measure.

Eval compute in .
Eval compute in bubble_sort (1 :: 2 :: 10 :: 3 :: 6 :: nil).