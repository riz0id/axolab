module Categorical.Category.Bundle.Monoidal where

open import Categorical.Category
open import Categorical.Category.Structure.Monoidal
open import Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record MonoidalCategory (o ℓ : Level) : Setoid (lsuc (o ⊔ ℓ)) where
  field
    U        : Category o ℓ
    monoidal : Monoidal U

  open module U        = Category U        public
  open module monoidal = Monoidal monoidal public
