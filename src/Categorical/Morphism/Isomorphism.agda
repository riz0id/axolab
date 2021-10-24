
open import Categorical.Category

module Categorical.Morphism.Isomorphism {o ℓ} (C : Category o ℓ) where

open import Prelude
open import Prelude.Equality

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
