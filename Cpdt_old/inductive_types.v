Inductive unit : Set :=
  | tt.

Check unit.
Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
Proof.
  induction x.
  reflexivity.
Qed.

Check unit_ind.

(* An inductive principle states that
   if a proposition P is true for (u : unit),
   then P is also true for all (u' : unit) *)

Inductive empty_set : Set := .

Theorem anything_at_all : forall x : empty_set, 2 + 2 = 5.
Proof.
  destruct 1.
Qed.

Check empty_set_ind.

(* fun way to convert from empty_set to unit *)
Definition e2u (e : empty_set) : unit := match e with end.

(* can create the booleans *)

Inductive bool : Set := | true | false .

Definition negb (b: bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

(* or *)

Definition negb' (b: bool) : bool :=
  if b then false else true.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
Proof.
  destruct b.
    reflexivity.
    reflexivity.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
  destruct b.
  discriminate.
  discriminate.
Qed.