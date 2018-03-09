-- Dependently Typed Metaprogramming in Agda
-- Following the notes by Connor McBride (2013)

-- CHAPTER 1. VECTORS AND NORMAL FUNCTORS
-- 1.1. Zipping lists of compatible shape

data List (X : Set) : Set where
  ⟨⟩  : List X
  _,_ : X → List X → List X
infixr 4 _,_

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
  
{-# BUILTIN NATURAL ℕ #-}

length : {X : Set} → List X → ℕ
length ⟨⟩       = zero
length (x , xs) = succ (length xs)


-- 1.2. Vectors and normal functors
data Vec (X : Set) : ℕ → Set where
  ⟨⟩ : Vec X zero
  _,_ : {n : ℕ} → X → Vec X n → Vec X (succ n)

data _×_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A × B

fst : forall {A B} → A × B → A
fst (a , b) = a
snd : forall {A B} → A × B → B
snd (a , b) = b

zip' : forall {n A B} → Vec A n → Vec B n → Vec (A × B) n
zip' ⟨⟩       ⟨⟩       = ⟨⟩
zip' (x , xs) (y , ys) = (x , y) , zip' xs ys

-- Exercise 1.1
vec : forall {n X} → X → Vec X n
vec {zero} x = ⟨⟩
vec {succ n} x = x , vec x

-- Exercise 1.2
vapp : forall {n A B} → Vec (A → B) n → Vec A n → Vec B n
vapp ⟨⟩       ⟨⟩       = ⟨⟩
vapp (f , fs) (s , ss) = (f s) , vapp fs ss

-- Exercise 1.3
vmap : forall {n A B} → (A → B) → Vec A n → Vec B n
vmap f xs = vapp (vec f) xs

-- Exercise 1.4
zip : forall {n A B} → Vec A n → Vec B n → Vec (A × B) n
zip ss ts = vapp (vmap _,_ ss) ts

-- Exercise 1.5
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (succ n)
  succ : {n : ℕ} → Fin n → Fin (succ n)

proj : forall {n X} → Vec X n → Fin n → X
proj ⟨⟩       ()
proj (x , xs) zero     = x
proj (x , xs) (succ i) = proj xs i

id : forall {k}{X : Set k} -> X -> X
id x = x

tabulate : forall {n X} → (Fin n → X) → Vec X n
tabulate {zero}   f = ⟨⟩
tabulate {succ n} f = f zero , vmap f (vmap succ (tabulate id))


-- 1.3. Applicative and traversable structure
_∘_ : forall {k}{A B C : Set k} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

record EndoFunctor (F : Set → Set) : Set₁ where
  field
    map : forall {A B} → (A → B) → F A → F B
open EndoFunctor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _⊛_
  field
    pure : forall {X} → X → F X
    _⊛_  : forall {A B} → F (A → B) → F A → F B
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record {map = _⊛_ ∘ pure}
open Applicative {{...}} public

applicativeVec : forall {n} → Applicative (λ X → Vec X n)
applicativeVec = record { pure = vec
                        ; _⊛_ = vapp
                        }
                        
endoFunctorVec : forall {n} → EndoFunctor (λ X → Vec X n)
endoFunctorVec = Applicative.applicativeEndoFunctor applicativeVec

applicativeFun : forall {Y} → Applicative (λ X → (Y → X))
applicativeFun = record { pure = λ x → λ y → x
                        ; _⊛_  = λ f → λ x → λ y → f y (x y)
                        }

record Monad (M : Set → Set) : Set₁ where
  field
    return : forall {A} → A → M A
    _>>=_  : forall {A B} → M A → (A → M B) → M B
  monadApplicative : Applicative M
  monadApplicative = record
    { pure = return
    ; _⊛_ = λ mf ma → mf >>= (λ f → ma >>= (return ∘ f))
    }
open Monad {{...}} public


-- Exercise 1.6
monadVec : {n : ℕ} → Monad (λ X → Vec X n)
monadVec = record { return = vec
                  ; _>>=_  = λ va → λ f → tabulate (λ n → proj (proj (vmap f va) n) n)
                  }


-- Exercise 1.7
applicativeId : Applicative id
applicativeId = record { pure = id; _⊛_ = id}

applicativeComp : forall { F G } → Applicative F → Applicative G → Applicative (F ∘ G)
applicativeComp aF aG = record { pure = pure {{aF}} ∘ pure {{aG}}
                               ; _⊛_ = _⊛_ {{aF}} ∘ map {{ applicativeEndoFunctor {{aF}} }} (_⊛_ {{aG}})
                               }
                       
-- Exercise 1.8
record Monoid (X : Set) : Set where
  infixr 4 _∙_
  field
    ε : X
    _∙_ : X → X → X
  monoidApplicative : Applicative λ _ → X
  monoidApplicative = record { pure = λ x → ε
                             ; _⊛_ = _∙_
                             }
open Monoid {{...}} public


-- Exercise 1.9
-- Pointwise product of applicatives is applicative
applicativeProd : forall { F G } → Applicative F → Applicative G → Applicative (λ A → F A × G A)
applicativeProd aF aG = record { pure = λ x → (pure {{aF}} x) , (pure {{aG}} x)
                               ; _⊛_ = λ f x → ((_⊛_ {{aF}} (fst f) (fst x)) , (_⊛_ {{aG}} (snd f) (snd x)))
                               }



-- Traversables
record Traversable (F : Set → Set) : Set₁ where
  field
    traverse : forall { G S T } {{ AG : Applicative G }} →
               (S → G T) → F S → G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record { map = traverse {{applicativeId}} }
open Traversable {{...}} public

traversableVec : {n : ℕ} → Traversable (λ X → Vec X n)
traversableVec = record { traverse = vtr } where
  vtr : forall {n G S T} {{_ : Applicative G}} →
        (S → G T) → Vec S n → G (Vec T n)
  vtr {{aG}} f ⟨⟩       = pure {{aG}} ⟨⟩
  vtr {{aG}} f (v , vs) = pure {{aG}} _,_ ⊛ f v ⊛ vtr f vs


-- Exercise 1.10
transpose : forall { m n X } → Vec (Vec X n) m → Vec (Vec X m) n
transpose {m} {n} {X} = traverse {{traversableVec}} {{applicativeVec}} id


data ⊤ : Set where
  ⋆ : ⊤

-- Crush operation
crush : forall {F X Y} {{TF : Traversable F}} {{M : Monoid Y}} →
        (X → Y) → F X → Y
crush {{M = M}} g m = traverse {T = ⊤} {{AG = monoidApplicative {{M}}}} g m


-- Exercise 1.11
traversableId : Traversable id
traversableId = record { traverse = id }

traversableComp : forall {F H} → Traversable F → Traversable H → Traversable (F ∘ H)
traversableComp tF tH = record {traverse = traverse {{tF}} ∘ traverse {{tH}}}


-- Chapter 1.4. Σ-types and other equipment
data Σ {l} (S : Set l) (T : S → Set l) : Set l where
  _,_ : (s : S) → T s → Σ S T

data Two : Set where
  tt : Two
  ff : Two

_<?>_ : forall {l} {P : Two → Set l} → P tt → P ff → (b : Two) → P b
(p <?> q) tt = p
(p <?> q) ff = q

_+_ : Set → Set → Set
S + T = Σ Two (S <?> T)

caseof : {P Q T : Set} → (P → T) → (Q → T) → (P + Q) → T
caseof f g (tt , x) = f x
caseof f g (ff , x) = g x

-- Chapter 1.5. Arithmetic
_+n_ : ℕ → ℕ → ℕ
zero +n y = y
succ x +n y = succ (x +n y)

_×n_ : ℕ → ℕ → ℕ
x ×n zero = zero
x ×n succ y = (x ×n y) +n x


-- Chapter 1.6. Normal functors
record Normal : Set₁ where
  constructor _/_
  field
    Shape : Set
    size  : Shape → ℕ
  ⟦_⟧ₙ : Set → Set
  ⟦_⟧ₙ X = Σ Shape (λ s → Vec X (size s))
open Normal public
infixr 0 _/_

-- Examples of normal functors
VecN : ℕ → Normal
VecN n = ⊤ / (λ _ → n)
ListN : Normal
ListN = ℕ / id
KN : Set → Normal
KN A = A / (λ _ → 0)
IKN : Normal
IKN = VecN 1

_+N_ : Normal → Normal → Normal
(ShF / szF) +N (ShG / szG) = (ShF + ShG) / caseof szF szG
_×N_ : Normal → Normal → Normal
(ShF / szF) ×N (ShG / szG) = (ShF × ShG) / (λ m → szF (fst m) +n szG (snd m))

nInj : forall {X} (F G : Normal) → ⟦ F ⟧ₙ X + ⟦ G ⟧ₙ X → ⟦ F +N G ⟧ₙ X
nInj F G (tt , s , x) = (tt , s) , x
nInj F G (ff , s , x) = (ff , s) , x
 

data _⁻¹ {S T : Set} (f : S → T) : T → Set where
  from : (s : S) → f ⁻¹ (f s)
