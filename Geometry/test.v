Axiom excluded_middle:
  forall P : Prop, P \/ ~ P.

Axiom proof_irrelevance:
  forall (P : Prop) (p q : P), p = q.

Axiom functional_extensionality:
  forall (A : Type) (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

Axiom propositional_extensionality:
  forall P Q : Prop, (P <-> Q) -> P = Q.

Axiom propositional_degeneracy:
  forall P : Prop, P = True \/ P = False.

Lemma add_assoc_S : forall m n : nat, m + S n = S (m + n).
Proof.
  intros m n.
  induction m as [|m]. destruct n as [|n].
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHm. reflexivity.
Qed.

Ltac simple_double_nat_induction :=
  intros m n;
  induction m as [|m]; induction n as [|n];
    simpl; reflexivity;
    simpl; reflexivity;
    simpl; rewrite IHm; reflexivity.

Lemma add_assoc_S : forall m n : nat, m + S n = S (m + n).
Proof.
  intros m n.
  induction m as [|m]. induction n as [|n].
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHm. reflexivity.
Qed.

Theorem add_comm : forall m n : nat, m + n = n + m.
Proof.
  intros m n.
  induction m. induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. simpl. reflexivity.
    simpl. rewrite IHm.
    rewrite (add_assoc_S n m).
    reflexivity.
Qed.