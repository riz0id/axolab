
module Axolab.Category.Bundle.CartesianCategory where

open import Axolab.Category
open import Axolab.Category.Structure.Cartesian
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record CartesianCategory (o ℓ : Level) : Setoid (lsuc (o ⊔ ℓ)) where
  eta-equality

  field
    U         : Category o ℓ
    cartesian : Cartesian U

  open Category U public
  open Cartesian cartesian public
