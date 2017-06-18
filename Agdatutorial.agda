module Agdatutorial where

open import Data.Nat public using (ℕ; zero; suc)

-- Boolean type
data Bool : Set where
  true : Bool
  false : Bool

-- Bottom type
data ⊥ : Set where

-- Unit type
data ⊤ : Set where
  tt : ⊤

-- data ℕ : Set where
--   zero : ℕ
--   suc : ℕ → ℕ

-- Binary trees
-- data BinTree : Set where
--   x : BinTree
--   _⊹_ : BinTree → BinTree → BinTree
  
data ListNat : Set where
  nilₙ : ListNat
  consₙ : ℕ → ListNat → ListNat

-- Mutually recursive sets
data L : Set
data M : Set

data L where
  nil : L
  _∷_ : ℕ → M → L
  
data M where
  _∷_ : Bool → L → M

-- Parametric sets
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_

-- Indexed sets
data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc : (n : ℕ) → Fin n → Fin (suc n)

data Inhabited : Bool → Set where
  top : Inhabited true

-- Propositions
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {n m : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

1≤10 : 1 ≤ 10
1≤10 = s≤s z≤n

data _isDoubleOf_ : ℕ → ℕ → Set where
  zd : zero isDoubleOf zero
  sd : {n : ℕ} → {m : ℕ} → n isDoubleOf m → suc (suc n) isDoubleOf (suc m)

8d4 : 8 isDoubleOf 4
8d4 = sd (sd (sd (sd zd)))

-- Negation?
not1d0 : 1 isDoubleOf 0 → ⊥
not1d0 = λ ()

not9d4 : 9 isDoubleOf 4 → ⊥
not9d4 (sd (sd (sd (sd a)))) = not1d0 a

open import Data.List using (List; []; _∷_)

-- Parameters vs indices
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data _∈_ {A : Set} : A → List A → Set where
  first : ∀ {x xs} → x ∈ (x ∷ xs)
  latter : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)


-- Functions defined by cases
not : Bool → Bool
not true = false
not false = true

_∧_ : Bool → Bool → Bool
(_∧_) true a = a 
(_∧_) false a = false


-- Recursive functions
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

mirroring : BinTree → BinTree
mirroring leaf = leaf
mirroring (node lt rt) = node rt lt

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

-- Polymorphic functions
map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = (f x) ∷ map f xs

swap : {A B : Set} → A × B → B × A
swap (a , b) = (b , a)


-- Functions to Sets
_≤′_ : ℕ → ℕ → Set
zero ≤′ n = ⊤
suc m ≤′ zero = ⊥
suc m ≤′ suc n = m ≤′ n

¬ : Set → Set
¬ A = A → ⊥


-- Dependently typed functions
fromℕ : (n : ℕ) → Fin (suc n)
fromℕ n = zero n

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  cons : ∀ {n} → A → Vec A n → Vec A (suc n)

head : ∀{A n} → Vec A (suc n) → A
head (cons a v) = a

tail : ∀{A n} → Vec A (suc n) → Vec A n
tail (cons a v) = v

last : ∀{A n} → Vec A (suc n) → A
last (cons a (cons b v)) = last (cons b v)
last (cons a []) = a

-- Universal Quantification
-- TODO
