Lemma equality_of_functions_commutes
  : forall (f : bool->bool) x y
  , (f x) = (f y) -> (f y) = (f x).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma xyz
  : forall (f : bool->bool) x y z
  , x = y -> y = z
 -> f x = f z.
Proof.
  intros.
  cut (x = z).
  intros.
  rewrite H1.
  reflexivity.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

