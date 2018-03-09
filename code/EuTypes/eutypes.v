(* Defining datatypes
*)
Inductive bool : Type :=
  | true : bool
  | false : bool.

(* and functions*)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Lemma andb_true_l : forall b : bool,
    andb true b = b.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma andb_true_r : forall b : bool,
    andb b true = b.
Proof.
  simpl. (* Does nothing it cannot use pattern matching as before*)
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.


(* Multiple tactics on a single line with ; *)
Lemma andb_comm : forall b1 b2 : bool,
    andb b1 b2 = andb b2 b1.
Proof.
  intros b1 b2.
  destruct b1; destruct b2; reflexivity.
Qed.

Lemma andb_assoc : forall b1 b2 b3 : bool,
    andb b1 (andb b2 b3) = andb (andb b1 b2) b3.
Proof.
  intros b1 b2 b3.
  destruct b1; reflexivity.
Qed.

(* Exercises on the web *)

(* Negation *)
Lemma true_neq_false : true <> false.
Proof.
  intros H.
  discriminate.
Qed.

(* We can use || to try two tactics *)
Lemma andb_true_inv : forall b1 b2,
  and b1 b2 = True -> b1 = True /\ b2 = True.
Proof.
  intros.
Admitted.

(* Inductive nat : Type := *)
(* | O : nat *)
(* | S : nat -> nat. *)

(* (* Recursion by structural induction *) *)
(* Fixpoint plus (n1 n2 : nat) : nat := *)
(*   match n1 with *)
(*   | O => n2 *)
(*   | S n1' => S (plus n1' n2) *)
(*   end. *)

(* Fixpoint mult (n1 n2 : nat) : nat := *)
(*   match n1 with *)
(*   | O => O *)
(*   | S n1' => plus n2 (mult n1' n2) *)
(*   end. *)

Lemma plus_0_l : forall n : nat,
    0 + n = n.
Proof.
  reflexivity.
Qed.

Lemma plus_0_r : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IH].
  - reflexivity.
  - simpl. f_equal. rewrite IH. reflexivity.
Qed.

Lemma plus_comm : forall n1 n2 : nat,
    n1 + n2 = n2 + n1.
Proof.                    
Admitted.


Lemma plus_assoc : forall n1 n2 n3 : nat,
    n1 + (n2 + n3) = (n1 + n2) + n3.
Proof.                    
Admitted.

Lemma plus_rearrange : forall n m p q : nat,
    (n + m) + p + q = (m + n) + (p + q).
Proof.
  intros.
  rewrite (plus_comm n m).
  rewrite <- (plus_assoc (m + n) p q).
  reflexivity.
Qed.

Inductive prod (A B : Type) : Type :=
| pair : A -> B -> prod A B.

Definition map_raw (A : Type) := list (option A).