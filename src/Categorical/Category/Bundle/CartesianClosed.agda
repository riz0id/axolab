
module Categorical.Category.Bundle.CartesianClosed where

open import Categorical.Category
open import Categorical.Category.Structure.Cartesian
open import Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record CartesianClosed (o ℓ : Level) : Setoid (lsuc (o ⊔ ℓ)) where
  field
    U               : Category o ℓ
    cartesianClosed : Cartesian U

  open module U = Category U public

  open module cartesianClosed = Cartesian cartesianClosed public
