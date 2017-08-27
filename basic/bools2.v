Require Import Bool.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
    case a, b.
      (* suppose a=true, b=true *)
      exact (or_introl I).
      (* suppose a=true, b=false *)
      exact (or_introl I).
      (* suppose a=false, b=true *)
      exact (or_intror I).
      (* suppose a=false, b=false *)
      case H.
  intros H.
  case a, b.
    (* suppose a=true, b=true *)
    exact I.
    (* suppose a=true, b=true *)
    exact I.
    (* suppose a=true, b=true *)
    exact I.
    case H.
      (* false -> false \/ false *)
      intros A.
      case A.
      (* false -> false \/ false *)
      intros B.
      case B.
Qed.

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
    case a, b.
      (* a=true, b=true *)
      exact (conj I I).
      (* a=true, b=false *)
      case H.
      (* a=false, b=true *)
      case H.
      (* a=false, b=false *)
      case H.
    intros H.
    case a, b.
      (* a=true, b=true *)
      exact I.
      (* a=true, b=false *)
      destruct H as [ A B ].
      case B.
      (* a=false, b=true *)
      destruct H as [ A B ].
      case A.
      (* a=false, b=false *)
      destruct H as [ A B ].
      case A.
Qed.

Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a)) ).
Proof.
  intros a.
  unfold iff.
  refine (conj _ _).
    case a.
      (* a=true *)
      simpl.
      intros H.
      case H.
      (* a=false *)
      simpl.
      intros H.
      intros A.
      case A.
    case a.
      (* a=true *)
      simpl.
      intros H.
      case H.
      exact I.
      (* a=false *)
      simpl.
      intros H.
      exact I.
Qed.