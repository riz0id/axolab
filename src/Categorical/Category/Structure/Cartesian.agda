module Categorical.Category.Structure.Cartesian where

open import Categorical.Category
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

record Cartesian {o ℓ} (C : Category o ℓ) : Setoid (o ⊔ ℓ) where
  infixr 5 _×_

  private
    open module C = Category C

  field
    _×₀_ : Ob → Ob → Ob
    _×₁_ : {A B C : Ob} → Hom A B → Hom A C → Hom A (B ×₀ C)

  field
    π₁ : {A B : Ob} → Hom (A ×₀ B) A
    π₂ : {A B : Ob} → Hom (A ×₀ B) B

  field
    π₁×₁≡id  : {A B C : Ob} (f : Hom A B) (g : Hom A C) → π₁ ∘ (f ×₁ g) ≡ f
    π₂×₁≡id  : {A B C : Ob} (f : Hom A B) (g : Hom A C) → π₂ ∘ (f ×₁ g) ≡ g

    ×-unique : {A B C : Ob} (f : Hom A B) (g : Hom A C) (h : Hom A (B ×₀ C))
      → f ≡ π₁ ∘ h → g ≡ π₂ ∘ h → h ≡ (f ×₁ g)
