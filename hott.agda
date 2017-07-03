-- CHAPTER 1. Type theory

-- SECTION 1.4. Dependent function types
-- The identity function is a polymorphic function
id : {A : Set} -> A -> A
id a = a

-- Swapping function
swap : {A B C : Set} -> (A -> B -> C) -> (B -> A -> C)
swap f y x = f x y



-- SECTION 1.12. Identity types
data _==_ {A : Set} : A → A → Set where
  refl : ∀ a → (a == a)

-- Path induction
ind₌ : {A : Set} →
       (C : {x y : A} → (x == y) → Set) →
       (c : (x : A) → C (refl x)) →
       {x y : A} → (p : x == y) → C p
ind₌ C c (refl x) = c x

  


-- SECTION 2.2. Functions are functors
ap : {A B : Set} → (f : A → B) → {x y : A} → (x == y) → (f x == f y)
ap f {x} {y} p = ind₌ (λ {a} {b} p → f a == f b) (λ u → refl (f u)) p


-- SECTION 1.5. Product types
data _×_ (P : Set) (Q : Set) : Set where
  _,_ : P → Q → (P × Q)

-- Recursor
rec_prod : {C : Set} → {A B : Set} → (A → B → C) → (A × B) → C
rec_prod f (a , b) = f a b

-- Projections
pr₁ : {A B : Set} → (A × B) → A
pr₁ = rec_prod(λ x → λ y → x)

pr₂ : {A B : Set} → (A × B) → B
pr₂ = rec_prod(λ x → λ y → y)

-- Uniqueness
uniqprod : {A B : Set} → (x : A × B) → (pr₁ x , pr₂ x) == x
uniqprod (a , b) = refl (a , b)

-- Induction
ind× : {A B : Set} →
       (C : A × B → Set) →
       ( ∀ x y → C ((x , y)) ) →
       (x : A × B) → C x
ind× C g (a , b) = g a b

-- SECTION 1.5. Unit type
data Unit : Set where
  ⋆ : Unit

ind⋆ : (C : Unit → Set) → C ⋆ → (x : Unit) → C x
ind⋆ C c ⋆ = c



-- SECTION 1.6. Dependent pair types
data Σ (A : Set) (B : A → Set) : Set where
  _of_ : (a : A) → (b : B a) → Σ A B

Σproj₁ : {A : Set} {B : A → Set} → (Σ A B) → A
Σproj₁ (a of b) = a

Σproj₂ : {A : Set} {B : A → Set} → (pair : Σ A B) → B (Σproj₁ pair)
Σproj₂ (a of b) = b



indΣ : {A : Set} {B : A → Set} →
       (C : Σ A B → Set) →
       ((a : A) → (b : B a) → C (a of b)) →
       (p : Σ A B) → C p
indΣ C g (a of b) = g a b


-- The recursor is a special case of the induction principle
recΣ : {A : Set} {B : A → Set} →
       (C : Set) →
       ((x : A) → B x → C) →
       Σ A B → C
recΣ C g (a of b) = indΣ (λ _ → C) g (a of b)


-- Type theoretic axiom of choice
ac : {A B : Set} {R : A → B → Set} →
     ( (x : A) → Σ B (R x) ) →
     Σ (A → B) (λ f → (x : A) → R x (f x))
ac g = (λ x → Σproj₁ (g x)) of (λ x → Σproj₂ (g x))


-- SECTION 1.6. Magmas
-- We cannot use Set : Set (!)
data Σ₁ (A : Set₁) (B : A → Set) : Set₁ where
  _of_ : (a : A) → (b : B a) → Σ₁ A B

Magma : Set₁
Magma = Σ₁ Set (λ A → (A → A → A))


-- SECTION 1.7. Coproduct types
data ⊥ : Set where

data _⨄_ (A : Set) (B : Set) : Set where
  inl : A → A ⨄ B
  inr : B → A ⨄ B

rec⨄ : {A B : Set} (C : Set) → (A → C) → (B → C) → (A ⨄ B → C)
rec⨄ C g₀ g₁ (inl a) = g₀ a
rec⨄ C g₀ g₁ (inr b) = g₁ b

rec₀ : (C : Set) → ⊥ → C
rec₀ C ()

ind⨄ : {A B : Set} →
       (C : (A ⨄ B) → Set) →
       ((a : A) → C (inl a)) →
       ((b : B) → C (inr b)) →
       (x : A ⨄ B) → C x
ind⨄ C g₀ g₁ (inl a) = g₀ a
ind⨄ C g₀ g₁ (inr b) = g₁ b

ind₀ : (C : ⊥ → Set) → (z : ⊥) → C z
ind₀ C ()


-- SECTION 1.8. The type of booleans
data Bool : Set where
  0₂ : Bool
  1₂ : Bool

recbool : (C : Set) → C → C → Bool → C
recbool C c₀ c₁ 0₂ = c₀
recbool C c₀ c₁ 1₂ = c₁

indbool : (C : Bool → Set) → C 0₂ → C 1₂ → (x : Bool) → C x
indbool C a b 0₂ = a
indbool C a b 1₂ = b


-- SECTION 1.9. The natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

double : ℕ → ℕ
double zero     = zero
double (succ n) = succ (succ (double n))

-- Recursor
recℕ : (C : Set) → C → (ℕ → C → C) → ℕ → C
recℕ C z s zero     = z
recℕ C z s (succ n) = s n (recℕ C z s n)

-- Induction
indℕ : (P : ℕ → Set) →
       P zero →
       ((n : ℕ) → P n → P (succ n)) →
       (n : ℕ) → P n
indℕ P h0 hs zero     = h0
indℕ P h0 hs (succ m) = hs m (indℕ P h0 hs m)

-- Addition
_+_ : ℕ → ℕ → ℕ
_+_ = recℕ (ℕ → ℕ) id (λ m f x → succ (f x))

assoc₀ : (j k : ℕ) → (zero + (j + k)) == ((zero + j) + k)
assoc₀ j k = refl (j + k)

assocₛ : (j k : ℕ) → (i : ℕ) →
         ((i + (j + k)) == ((i + j) + k)) →
         ((succ i) + (j + k)) == (((succ i) + j) + k)
assocₛ j k i h = ap succ h

assoc : (i j k : ℕ) → (i + (j + k)) == ((i + j) + k)
assoc i j k = indℕ (λ x → (x + (j + k)) == ((x + j) + k)) (assoc₀ j k) (assocₛ j k) i


-- SECTION 1.10

-- SECTION 1.11
¬ : Set → Set
¬ A = (A → ⊥)

morgan : {A B : Set} → ¬ (A ⨄ B) → ((¬ A) × (¬ B))
morgan f = (λ a → f (inl a)) , (λ b → f (inr b))


-- SECTION 1.12
-- Disequality
_≠_ : {A : Set} → A → A → Set
_≠_ x y = (x == y) → ⊥

-- Semigroups
Semigroup : Set₁
Semigroup = Σ₁ Set (λ A → Σ (A → A → A) (λ m → (x y z : A) → ((m x (m y z)) == (m (m x y) z)) ))


-- Section 1 Exercises
-- Exercise 1.1
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
_∘_ g f x = g (f x)

composition-assoc : {A B C D : Set} →
                    (f : A → B) → (g : B → C) → (h : C → D) →
                    (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)
composition-assoc f g h = refl (λ x → h (g (f x)))

-- Exercise 1.11
tripleneg : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
tripleneg f a = f (λ g → g a)

-- Exercise 1.13
doublenegexcluded : {A : Set} → ¬ (¬ (A ⨄ (¬ A)))
doublenegexcluded f = f (inr (λ a → f (inl a)))
                          
                    
