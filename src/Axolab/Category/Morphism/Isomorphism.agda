
open import Axolab.Category

module Axolab.Category.Morphism.Isomorphism {o ℓ} (C : Category o ℓ) where

open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

infix 4 Isomorphism

open Category C

syntax Isomorphism X Y = X ≅ Y

record Isomorphism (X Y : Ob) : Setoid (o ⊔ ℓ) where
  eta-equality
  field
    from : Hom X Y
    to   : Hom Y X
    iso← : to ∘ from ≡ id
    iso→ : from ∘ to ≡ id
