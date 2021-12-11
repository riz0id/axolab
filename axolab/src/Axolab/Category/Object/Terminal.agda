
open import Axolab.Category

module Axolab.Category.Object.Terminal {o ℓ} (C : Category o ℓ) where

open import Axolab.Prelude

open Category C

-- ---------------------------------------------------------------------------------------------------------------------

record Terminal  : Set (o ⊔ ℓ) where
  field
    ⊤        : Ob
    terminal : {A : Ob} → isContr (Hom A ⊤)

  ! : {A : Ob} → Hom A ⊤
  ! = center terminal

  !-unique : {A : Ob} (f : Hom A ⊤) → ! ≡ f
  !-unique = paths terminal

  !-unique₂ : {A : Ob} (f g : Hom A ⊤) → f ≡ g
  !-unique₂ f g = sym (!-unique f) ∘p !-unique g
