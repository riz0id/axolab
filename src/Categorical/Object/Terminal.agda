
module Categorical.Object.Terminal where

open import Categorical.Category
open import Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record Terminal {o ℓ} (C : Category o ℓ) : Setoid (lsuc (o ⊔ ℓ)) where
