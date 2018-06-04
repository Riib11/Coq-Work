Class Hilbert_neutral_2D :=
{
  Point  : Type;
  Line   : Type;
  EqLine : Line -> Line -> Prop;
  Incidental : Point -> Line -> Prop;

  l0 : Line;
  P0 : Point;
  plan : ~ Incidental P0 l0;

  Incidental_morphism:
    forall P l m,
    Incidental P l -> EqLine l m -> Incidental P m;

  Incidental_decidable:
    forall P l,
    Incidental P l \/ Incidental P l;


  point_equality_decidable:
    forall A B : Point, A = B \/ ~ A = B;

  (***********************
   * Group I - Incidence *
   ***********************)

  line_existence:
    forall A B,
    A <> B -> exists l, Incidental A l /\ Incidental B l;

  line_uniqueness:
    forall A B l m,
    A <> B ->
    Incidental A l -> Incidental B l -> Incidental A m -> Incidental B m ->
    EqLine l m;

  two_points_on_line:
    forall l,
      { A : Point &
      { B : Point
      | Incidental B l /\ Incidental A l /\ A <> B }};

  Colinear:
    Point -> Point -> Point -> Prop :=
    fun A B C =>
    exists l, Incidental A l /\ Incidental B l /\ Incidental C l;

  (********************
   * Group II - Order *
   ********************)

  Between : Point -> Point -> Point -> Prop;

  between_colinear : forall A B C, Between A B C -> Colinear A B C;
  between_neq : forall A B C, Between A B C -> A <> C;
  between_commutative : forall A B C, Between A B C -> Between C B A;
  between_out : forall A B, A <> B -> exists C, Between B C A;
  between_only_one : forall A B C, Between A B C -> ~ Between B C A;

  cut: Line -> Point -> Point -> Prop :=
    fun l A B =>
      ~ Incidental A l /\ ~ Incidental B l /\
      exists I, Incidental I l /\ Between A I B;

  pasch:
    forall A B C l,
    ~ Colinear A B C -> ~ Incidental C l -> cut l A B ->
    cut l A C \/ cut l B C;

   (*************************
   * Group III - Congruence *
   **************************)

  Congruent : Point -> Point -> Point -> Point -> Prop;
  congruent_permutation : forall A B C D, Congruent A B C D -> Congruent A B D C;
  congruent_pseudotransitive:
    forall A B C D E F,
    Congruent A B C D -> Congruent A B E F -> Congruent C D E F;

  out: Point -> Point -> Point -> Prop :=
    fun P A B => Between P A B \/ Between P B A \/ (P <> A /\ A = B);

  congruent_existence:
    forall A B A' P l,
    A <> B -> A' <> P ->
    Incidental A' l -> Incidental P l ->
    exists B', Incidental B' l /\ out A' P B' /\ Congruent A' B' A B;

  disjoint : Point -> Point -> Point -> Point -> Prop :=
    fun A B C D => ~ exists P, Between A P B /\ Between C P D;

  addition :
    forall A B C A' B' C',
    disjoint A B B C -> disjoint A' B' B' C' ->
    Congruent A B A' B' -> Congruent B C B' C' ->
    Congruent A C A' C';

  ConruentArea: Point -> Point -> Point -> Point -> Point -> Point -> Prop;

  congruentarea_reflection : forall A B C, ~ Colinear A B C -> CongruentArea A B C A B C;
  congruentarea_commutative : forall A B C, ~ Colinear A B C -> CongruentArea A B C C B A;

}.

Check xxx.