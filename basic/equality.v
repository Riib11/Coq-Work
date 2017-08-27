Require Import Bool.

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
  intros x y.
  intros x_eq_y.
  destruct x_eq_y as [].
  exact (eq_refl x).
Qed.

Theorem thm_eq_trans : (forall x y z: Set, x = y -> y = z -> z = x).
Proof.
  intros x y z.
  intros x_eq_y y_eq_z.
  destruct x_eq_y as [].
  destruct y_eq_z as [].
  exact (eq_refl x).
Qed.

Theorem thm_trans_trans_again : (forall x y z : Set, x = y -> y = z -> z = x).
Proof.
  intros x y z.
  intros x_eq_y y_eq_z.
  rewrite x_eq_y.
  rewrite y_eq_z.
  exact (eq_refl z).
Qed.

Theorem andb_sym : (forall a b, a && b = b && a).
Proof.
  intros a b.
  case a, b.
    simpl.
    exact (eq_refl true).
    simpl.
    exact (eq_refl false).
    simpl.
    exact (eq_refl false).
    simpl.
    exact (eq_refl false).
Qed.