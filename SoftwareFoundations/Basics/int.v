Search True.
Search False.
Search bool.

Inductive int : Set :=
  | Z  : int         (*  0      *)
  | Zp : int -> int  (*  x + 1  *)
  | Zn : int -> int. (*  x - 1  *)

Fixpoint zplus (x y:int) : int :=
  match x with
  | Z    => y              (* 0     + y = y           *)
  | Zp x => Zp (zplus x y) (* (x+1) + y = (x + y) + 1 *)
  | Zn x => Zn (zplus x y) (* (x-1) + y = (x + y) - 1 *)
  end.

Fixpoint zminus (x y:int) : int :=
  match y with
  | Z    => x               (* x - 0     = x           *)
  | Zp y => Zn (zminus x y) (* x - (y+1) = (x - y) + 1 *)
  | Zn y => Zp (zminus x y) (* x - (y-1) = (x - y) - 1 *)
  end.

Theorem zplus_id_right : forall x:int, zplus x Z = x.
Proof.
  intros.
  induction x.
    simpl. reflexivity.
    simpl. rewrite IHx. reflexivity.
    simpl. rewrite IHx. reflexivity.
Qed.

Fixpoint zmult (x y:int) : int :=
  match x with
  | Z => Z                       (* 0 * y     = 0         *)
  | Zp x => zplus  (zmult x y) y (* (x+1) * y = (x*y) + y *)
  | Zn x => zminus (zmult x y) y (* (x-1) * y = (x*y) - y *)
  end.

Theorem zmult_zero_right : forall x:int, zmult x Z = Z.
Proof.
  intros.
  induction x.
    simpl. reflexivity.
    simpl. rewrite IHx. reflexivity.
    simpl. rewrite IHx. reflexivity.
Qed.

(*

N_rec:
  forall P : N -> Set,
  P O -> (forall n : N, P n -> P (S n)) -> forall n : N, P n.

bool_rec:
  forall P : bool -> Set,
  P true -> P false -> forall b : bool, P b

N_ind:
  forall P : N -> Prop,
  P O -> (forall n : N, P n -> P (S n)) -> forall n : N, P n

bool_ind:
  forall P : bool -> Prop,
  P true -> P false -> forall b : bool, P b.

*)