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
ind× : {A B : Set} → (C : A × B → Set) → ( ∀ x y → C ((x , y)) ) → (x : A × B) → C x
ind× C g (a , b) = g a b

-- SECTION 1.5. Unit type
data Unit : Set where
  ⋆ : Unit

ind⋆ : (C : Unit → Set) → C ⋆ → (x : Unit) → C x
ind⋆ C c ⋆ = c

