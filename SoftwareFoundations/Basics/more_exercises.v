(* Exercise 1 *)
Theorem identity_fn_applied_twice :
  forall f : bool -> bool,
  (forall x : bool, f x = x) ->
  forall b : bool, f (f b) = b.
Proof.
  intros f f_id b.
  rewrite f_id.
  rewrite f_id.
  reflexivity.
Qed.

(* Exercise 2 *)
Theorem andb_eq_orb :
  forall b c : bool,
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c H.
  destruct b.
    (* true, true *)
    destruct c.
    reflexivity.
    (* true, false *)
    simpl in H.
    discriminate.
    (* false, true *)
    destruct c.
    simpl in H.
    discriminate.
    (* false, false *)
    simpl in H.
    exact H.
Qed.

(* Exercise 3 *)
Inductive bin : Type :=
  | bZ : bin
  | bE : bin -> bin
  | bO : bin -> bin.

Fixpoint incr (b:bin) : bin :=
  match b with
  | bZ   => bO bZ
  | bE x => bO x
  | bO x => bE (incr x)
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
  | bZ    => O
  | bE x  => 2 * (bin_to_nat x)
  | bO x  => 2 * (bin_to_nat x) + 1
  end.

Lemma add_id_right : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma add_associativity : forall m n o : nat, m + (n + o) = m + n + o.
Proof.
  intros m n o.
  induction m. induction n. induction o.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite IHm. reflexivity.
Qed.

Lemma add_commutativity :
  forall a b c d : nat,
  a + b + c + d = a + c + b + d.
Admitted.

Theorem incr_correct : forall b, bin_to_nat (incr b) = bin_to_nat b + 1.
Proof.
  intro b.
  induction b.
    (* bZ *)
    simpl. reflexivity.
    (* bE *)
    simpl. rewrite add_id_right. reflexivity.
    (* bO *)
    simpl. rewrite add_id_right.
    rewrite IHb. rewrite add_id_right.
    rewrite add_associativity.
    rewrite add_commutativity.
    reflexivity.
Qed.