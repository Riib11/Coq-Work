(* Require Export Field_theory. *)
Require Import ZArith.
Open Scope Z_scope.

Goal forall a b c : Z,
  (a+b+c)^2 =
  a * a + b^2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
  intros.
  ring.
Qed.