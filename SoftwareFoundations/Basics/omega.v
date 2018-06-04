Require Import Omega.

Lemma odds_arent_even
  : forall (a b : nat)
  , 2 * a + 1 <> 2 * b.
Proof.
  intros.
  omega.
Qed.

