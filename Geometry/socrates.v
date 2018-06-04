(* "Human" is a thing. *)
Axiom Human  : Type.
(* "This human is mortal" is a proposition. *)
Axiom Mortal : Human -> Prop.

(* It is given that "all humans are mortal" has a proof. *)
Axiom all_humans_mortal :
  forall h : Human, Mortal h.

(* It is given that Socrates is a human *)
Axiom socrates : Human.

(* It results that Socrates is mortal *)
Theorem socrates_mortal : Mortal socrates.
Proof.
  exact (all_humans_mortal socrates).
Qed.