
module Categorical.Category.Bundle.Cartesian where

open import Categorical.Category
open import Categorical.Category.Structure.Cartesian
open import Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record CartesianCategory (o ℓ : Level) : Setoid (lsuc (o ⊔ ℓ)) where
  field
    U  : Category o ℓ
    ca : Cartesian U

  open module U  = Category  U  public
  open module ca = Cartesian ca public
