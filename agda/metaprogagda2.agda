-- CHAPTER 2. Simply typed λ-calculus
open import Data.Nat.Base
open import Data.Unit.Base
open import Data.Product

-- Section 2.1. Syntax
-- Types
data ⋆ : Set where
  ι   : ⋆
  _▷_ : ⋆ → ⋆ → ⋆
infixr 5 _▷_


-- Contexts
data Cx (X : Set) : Set where
  Emp : Cx X
  _,_ : Cx X → X → Cx X
infixl 4 _,_

data _∈_ (τ : ⋆) : Cx ⋆ → Set where
  zero : forall {Γ}           → τ ∈ (Γ , τ)
  suc  : forall {Γ σ} → τ ∈ Γ → τ ∈ (Γ , σ)
infix 3 _∈_


-- Well-typed λ-terms
data _⊢_ (Γ : Cx ⋆) : ⋆ → Set where

  var : forall {τ}
        → τ ∈ Γ
        ---------
        → Γ ⊢ τ
        
  lam : forall {σ τ}
        → (Γ , σ) ⊢ τ
        ---------------
        → Γ ⊢ (σ ▷ τ)

  app : forall {σ τ}
        → Γ ⊢ (σ ▷ τ)
        → Γ ⊢ σ
        -------------
        → Γ ⊢ τ

infix 3 _⊢_




-- Section 2.2. Semantics
-- Semantic of basic types
⟦_⟧ₛ : ⋆ → Set
⟦ ι ⟧ₛ     = ℕ
⟦ σ ▷ τ ⟧ₛ = ⟦ σ ⟧ₛ → ⟦ τ ⟧ₛ

-- Environments for contexts
⟦_⟧ₓ : Cx ⋆ → (⋆ → Set) → Set
⟦ Emp   ⟧ₓ V = ⊤
⟦ Γ , σ ⟧ₓ V = ⟦ Γ ⟧ₓ V × V σ

⟦_⟧ₚ : forall {Γ τ V} → τ ∈ Γ → ⟦ Γ ⟧ₓ V → V τ
⟦ zero ⟧ₚ  (γ , t) = t
⟦ suc n ⟧ₚ (γ , t) = ⟦ n ⟧ₚ γ

-- Meaning of terms
⟦_⟧ᵢ : forall {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ₓ ⟦_⟧ₛ → ⟦ τ ⟧ₛ
⟦ var x ⟧ᵢ   γ = ⟦ x ⟧ₚ γ
⟦ lam t ⟧ᵢ   γ s = ⟦ t ⟧ᵢ (γ , s)
⟦ app t r ⟧ᵢ γ = ⟦ t ⟧ᵢ γ (⟦ r ⟧ᵢ γ)

