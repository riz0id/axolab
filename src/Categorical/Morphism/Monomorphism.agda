
open import Categorical.Category

module Categorical.Morphism.Monomorphism {o ℓ} (C : Category o ℓ) where

open import Prelude
open import Prelude.Equality

open Category C

private
  variable
    X A : Ob
    g₁ g₂ : Hom X A

-- ---------------------------------------------------------------------------------------------------------------------

infixr 2 Monomorphism

syntax Monomorphism A B = A ↪ B

record Monomorphism (A B : Ob) : Setoid (o ⊔ ℓ) where
  field
    into  : Hom A B
    monic : into ∘ g₁ ≡ into ∘ g₂ → g₁ ≡ g₂
