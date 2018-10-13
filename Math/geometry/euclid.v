(*–––––––––––––––––––––––––––––––––––+
 |
 |  Euclid's Axioms for Geometry
 |
 +–––––––––––––––––––––––––––––––––––*)


(* Basic Types *)
Axiom Point : Set.

(* Axiom 1 *)
Inductive Segment : Set :=
  segment_from_points : Point -> Point -> Segment.

(* Axiom 2 *)
Inductive Line : Set :=
  line_from_segment : Segment -> Line.

(* Axiom 3 *)
Inductive Circle : Set :=
  circle_from_points : Point -> Point -> Circle.

(* Axiom 4 *)
Axiom Angle : Set.
Axiom angle_between : Line -> Line -> Angle.
Axiom right : Angle.

Axiom lines_angles_equality:
  forall l l' l'' : Line,
  angle_between l l'  = angle_between l l''
  -> l' = l''.

Proposition lines_right_angles_equality:
  forall l l' l'',
  angle_between l l'  = right
  -> angle_between l l'' = right
  -> l' = l''.
Proof.
  intros.
  cut (angle_between l l' = angle_between l l''). intro.
  apply (lines_angles_equality l l' l'' H1).
  pose (H1 := eq_sym H0).
  apply (eq_trans H H1).
Qed.

Inductive right_angled : Line -> Line -> Prop :=
  right_lines : forall l l', angle_between l l' = right -> right_angled l l'.

(* Axiom 5 *)
Axiom nonperpendicular_lines_intersect:
  forall l l',
  ~ right_angled l l' 

