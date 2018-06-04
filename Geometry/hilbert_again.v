(*************************
 * Group 0 - Definitions *
 *************************)

Axiom Point  : Type.
Axiom Line   : Type.
(*Axiom Plane  : Type*)

(* Line Equality *)
Axiom EqLine : Line -> Line -> Prop.

(* Point-Line Congruence *)
Axiom Cong : Point -> Point -> Point -> Point -> Prop.

(* Incidental Lines *)
Axiom Incide : Point -> Line -> Prop.

(* Colinear Points *)
Definition Coline : Point -> Point -> Point -> Prop :=
  fun A B C =>
  exists l, Incide A l /\ Incide B l /\ Incide C l.

(* Between Points *)
Axiom Between : Point -> Point -> Point -> Prop.

Axiom point_equality_decidable:
  forall A B : Point, A = B \/ ~ A = B.

Axiom incidental_eqline_morphism:
  forall P l m,
  Incide P l -> EqLine l m -> Incide P m.

Axiom incidental_decidable:
  forall P l,
  Incide P l \/ ~ Incide P l.

(***********************
 * Group 1 - Incidence *
 ***********************)

Axiom line_existence:
  forall A B,
  A <> B -> exists l, Incide A l /\ Incide B l.

Axiom line_uniqueness:
  forall A B l m,
  Incide A l /\ Incide B l ->
  Incide A m /\ Incide B m ->
  EqLine m l.

Axiom two_point_line_existence:
  exists A B l,
  Incide A l /\ Incide B l.

Axiom three_point_line_not_incidental:
  exists A B C l,
  ~ ( Incide A l /\ Incide B l /\ Incide C l ).

(*******************
 * Group 2 - Order *
 *******************)

Axiom between_colinear:
  forall A B C, A <> B /\ B <> C ->
  Between A B C ->
  Coline A B C.

Axiom between_neq:
  forall A B C,
  Between A B C -> A <> C.

Axiom between_commutative:
  forall A B C,
  Between A B C -> Between C B A.

Axiom between_exists:
  forall A C, A <> C ->
  exists B, Between A B C.

Axiom between_unique:
  forall A B C,
  Between A B C -> ~ Between B C A.

Definition cut: Line -> Point -> Point -> Prop :=
  fun l A B =>
    ~ (Incide A l \/ Incide B l) /\
    exists I, Incide I l /\ Between A I B.

Axiom pasch:
  forall A B C l,
  ~ Coline A B C -> ~ Incide C l -> cut l A B ->
  cut l A C \/ cut l B C.

Definition disjoint : Point -> Point -> Point -> Point -> Prop :=
  fun A B C D => ~ exists P, Between A P B /\ Between C P D.

(************************
 * Group 3 - Congruence *
 ************************)

Axiom congruence_intro:
  forall A B A' l l',
  Incide A l /\ Incide B l ->
  Incide A' l' ->
  exists B', Cong A B A' B'.

Axiom congruence_permutation : forall A B C D, Cong A B C D -> Cong A B D C.

Axiom congruence_pseudotransitive:
  forall A B C D E F,
  Cong A B C D -> Cong A B E F -> Cong C D E F.

Axiom congruence_addition:
  forall A B C A' B' C',
  A  <> B  /\ A  <> C  ->
  A' <> B' /\ A' <> C' ->
  Cong A B A' B' /\ Cong B C B' C' -> Cong A C A' C'.

(****************************
 * Group 4 - Parallel Lines *
 ****************************)

Definition parallel: Line -> Line -> Prop :=
  fun l l' => ~ exists X, Incide X l /\ Incide X l'.

Axiom parallel_unique:
  forall A l l1 l2,
  ~ Incide A l ->
  parallel l l1  -> Incide A l1  ->
  parallel l l2 -> Incide A l2 ->
  EqLine l1 l2.

(************************
 * Group 5 - Continuity *
 ************************)

(* TODO *)