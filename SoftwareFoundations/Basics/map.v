Import Nat.

Module PartialMap.

Inductive id : Type :=
  | Id : nat -> id.

Definition eqb_id k k' :=
  match k,k' with
  | Id n, Id n' => n =? n'
  end.

Definition beq_id x y : bool :=
  match x,y with
  | Id a, Id b => eqb a b
  end.

Theorem eqb_refl : forall x, eqb x x = true.
Proof.
  intros.
  induction x.
    simpl. reflexivity.
    simpl. rewrite IHx. reflexivity.
Qed.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  intros.
  destruct x as [x].
  destruct x.
    simpl. reflexivity.
    simpl. rewrite eqb_refl. reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update m k v : partial_map :=
  record k v m.

Fixpoint find k m : option nat :=
  match m with
  | empty => None
  | record k' v m' =>
      if eqb_id k k'
      then Some v
      else find k m'
  end.

Theorem update_eq : forall m k v, find k (update m k v) = Some v.
Proof.
  intros.
  induction m.
    simpl. rewrite eqb_id_refl. reflexivity.
    simpl. rewrite eqb_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall m k k' v,
  eqb_id k k' = false -> 
  find k (update m k' v) = find k m.
Proof.
  intros.
  induction m.
    simpl. rewrite H. reflexivity.
    simpl. rewrite H. reflexivity.
Qed.

End PartialMap.