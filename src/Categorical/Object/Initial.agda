open import Categorical.Category

module Categorical.Object.Initial {o ℓ} (C : Category o ℓ) where

open import Prelude
open import Prelude.Equality

open Category C

private
  variable
    A : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Initial : Setoid (o ⊔ ℓ) where
  field
    ⊥       : Ob
    initial : isContr (Hom ⊥ A)

  ! : Hom ⊥ A
  ! = center initial

  !-unique : (f : Hom ⊥ A) → ! ≡ f
  !-unique = paths initial

  !-unique₂ : (f g : Hom ⊥ A) → f ≡ g
  !-unique₂ f g = sym (!-unique f) ∘p !-unique g
