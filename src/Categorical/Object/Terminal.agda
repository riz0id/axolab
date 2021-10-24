
module Categorical.Object.Terminal where

open import Categorical.Category
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

record Terminal {o ℓ} (C : Category o ℓ) : Setoid (o ⊔ ℓ) where
  private
    open module C = Category C

  field
    ⊤        : Ob
    terminal : {A : Ob} → isContr (Hom A ⊤)

  ! : {A : Ob} → Hom A ⊤
  ! = center terminal

  !-unique : {A : Ob} (f : Hom A ⊤) → ! ≡ f
  !-unique = paths terminal

  !-unique₂ : {A : Ob} (f g : Hom A ⊤) → f ≡ g
  !-unique₂ f g = sym (!-unique f) ∘p !-unique g
