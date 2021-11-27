
open import Axolab.Category

module Axolab.Category.Morphism.Monomorphism {o ℓ} (C : Category o ℓ) where

open import Axolab.Prelude

open Category C

private
  variable
    X A : Ob
    g₁ g₂ : Hom X A

-- ---------------------------------------------------------------------------------------------------------------------

infixr 2 Monomorphism

syntax Monomorphism A B = A ↪ B

record Monomorphism (A B : Ob) : Set (o ⊔ ℓ) where
  field
    into  : Hom A B
    monic : into ∘ g₁ ≡ into ∘ g₂ → g₁ ≡ g₂
