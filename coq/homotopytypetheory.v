(* Exercise 1.1. *)
(* Given functions f : A → B and g : B → C, define their composite
g ∘ f : A → C. Show that we have h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f.*)

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : (A -> C) :=
  (fun x => g(f(x))).

Notation "g ∘ f" := (compose g f) (at level 60, right associativity).

Theorem composeassoc {A B C D : Type} (h: C -> D) (g: B -> C) (f: A -> B) :
  (h ∘ (g ∘ f)) = ((h ∘ g) ∘ f).
Proof.
  unfold compose.
  reflexivity.
Qed.


(* Exercise 1.2. *)
(* Derive the recursion principle for products rec, using only the projections,
and verify that the definitional equalities are valid. Do the same for Σ types. *)
