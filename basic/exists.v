Require Import Bool.

Definition basic_predicate := (fun a => Is_true (andb a true)).

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    exact I.
Qed.

Theorem thm_exists_basics_again : (exists a, Is_true (andb a true)).
Proof.
  pose (witness := true).
  refine (ex_intro _ witness _).
    exact I.
Qed.

Theorem thm_forall_exists : (forall b, (exists a, Is_true (eqb a b)) ).
Proof.
  intros b.
  case b.
    (* b=true *)
    pose (witness := true).
    refine (ex_intro _ witness _).
    exact I.
    (* b=false *)
    pose (witness := false).
    refine (ex_intro _ witness _).
    exact I.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    (* suppose a is true *)
    simpl.
    exact I.
    (* suppose a is false. *)
    simpl.
    exact I.
Qed.

Theorem thm_forall_exists_again : (forall b, (exists a, Is_true( eqb a b)) ).
Proof.
  intros b.
  refine (ex_intro _ b _).
  (* witness := b *)
  exact (eqb_a_a b).
Qed.