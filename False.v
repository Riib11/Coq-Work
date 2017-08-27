(* Theorem False_is_unprovable : ~False.
Proof.
  unfold not. (* this unfolds the notation ~ *)
  intros proof_False.
  exact proof_False.
Qed. *)

Theorem False_is_unprovable_again : ~False.
Proof.
  intros proof_False.
  case proof_False. (* this creates all the possible subgoals of the current subgoal. since there are no possible subgoals for proving False, we're done! *)
Qed.