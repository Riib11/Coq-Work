Require Import Arith_base.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.

Inductive sortedlist : nat -> Type :=
  | nil : sortedlist 0
  | cons : forall (m n : nat), sortedlist m -> m <= n -> sortedlist n.

Theorem zero_leq_all : forall (m : nat), 0 <= m.
  intros.
  induction m.
    apply le_n.
    apply le_S.
    apply IHm.
Qed.

Theorem zero_leq_1 : 0 <= 1. apply zero_leq_all. Qed.

Definition sortedlist_01 : sortedlist 1 := cons 0 1 nil zero_leq_1.

