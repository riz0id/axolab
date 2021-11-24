
module Axolab.Category.Bundle.MonoidalCategory where

open import Axolab.Category
open import Axolab.Category.Structure.Monoidal
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record MonoidalCategory (o ℓ : Level) : Setoid (lsuc (o ⊔ ℓ)) where
  eta-equality

  field
    U        : Category o ℓ
    monoidal : Monoidal U

  open Category U public
  open Monoidal monoidal public
