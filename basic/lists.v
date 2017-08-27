Require Import List.

Theorem cons_adds_one_to_length :
  (forall A : Type,
  (forall (x : A) (lst : list A),
  length (x :: lst) = (S (length lst)))).
Proof.
  intros A x lst.
  simpl.
  exact (eq_refl (S(length lst))).
Qed.

Definition my_hd := hd nat nil.

Definition hd_error (A : Type) (l : list A) :=
  match l with
    | nil => None
    | x :: _ => Some x
  end.

Theorem correctness_hd_error :
  (forall A : Type,
  (forall (x : A) (l : list A),
  (hd_error A nil) = None /\ (hd_error A (x::l)) = Some x)).
Proof.
  intros A x l.
  refine (conj _ _).
    simpl.
    exact (eq_refl None).

    simpl.
    exact (eq_refl (Some x)).
Qed.

Definition hd_neverfail (A : Type) (l : list A) (safety_proof : l <> nil) : A :=
  (match l as b return (l = b -> A) with
    | nil => (fun foo: l = nil =>
                    match (safety_proof foo) return A with
                    end
              )
    | x :: _ => (fun foo : l = x :: _ =>
                    x
                )
  end) eq_refl.

Theorem correctness_hd_neverfail :
  (forall A : Type,
  (forall (x : A) (rest : list A),
  (exists safety_proof : ((x::rest) <> nil),
    (hd_neverfail A (x::rest) safety_proof) = x))).
Proof.
  intros A x rest.
  assert (witness : ((x::rest) <> nil)).
    unfold not.
    intros cons_eq_nil.
    discriminate cons_eq_nil.
  refine (ex_intro _ witness _).
    simpl.
    exact (eq_refl x).
Qed.

(* the xs in (x::xs) *)
Definition tl (A : Type) (l:list A) :=
  match l with
    | nil => nil
    | a :: m => m
  end.