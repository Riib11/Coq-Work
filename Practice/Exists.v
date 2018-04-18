Lemma nat_succ_plus_1 : forall x, x + 1 = S x.
Proof.
  intros.
  induction x.
    simpl.
    reflexivity.
    simpl.
    rewrite IHx.
    reflexivity.
Qed.

Lemma L1 : forall x, exists y, x + y = S x.
Proof.
  intros.
  exists 1.
  rewrite nat_succ_plus_1.
  reflexivity.
Qed.