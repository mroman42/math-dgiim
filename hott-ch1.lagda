\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_])

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

double : Nat → Nat
double zero = zero
double (succ n) = succ (succ (double n))

add : Nat → Nat → Nat
add zero     n = n
add (succ m) n = succ (add m n)

rec-Nat : {C : Set} → C → (Nat → C → C) → Nat → C
rec-Nat {C} c0 cs zero     = c0
rec-Nat {C} c0 cs (succ n) = cs n (rec-Nat c0 cs n)

ind-Nat : {C : Nat → Set} → C zero → ( (n : Nat) → C n → C (succ n) ) → (n : Nat) → C n
ind-Nat c0 cs zero     = c0
ind-Nat c0 cs (succ n) = cs n (ind-Nat c0 cs n)

assoc₀ : (j : Nat) → (k : Nat) → add zero (add j k) ≡ add (add zero j) k
assoc₀ = λ j k → refl

assocₛ : (i : Nat) →
         ( (j : Nat) → (k : Nat) → add i (add j k) ≡ add (add i j) k) →
         ( (j : Nat) → (k : Nat) → add (succ i) (add j k) ≡  add (add (succ i) j) k )
assocₛ i h j k = cong succ (h j k)

assoc : (i : Nat) → (j : Nat) → (k : Nat) → add i (add j k) ≡ add (add i j) k
assoc i = ind-Nat assoc₀ assocₛ i
\end{code}
