Axiom f : False.

Theorem what : true = false.
Proof.
  pose (pf_False := f).
  case f.
Qed.

Check False.

Inductive X := | a | b.

Search and.