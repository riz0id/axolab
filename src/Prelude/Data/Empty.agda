
module Prelude.Data.Empty where

open import Prelude

-- ---------------------------------------------------------------------------------------------------------------------

data Bot {ℓ} : Setoid ℓ where

absurd : {ℓ₁ ℓ₂ : Level} {A : Setoid ℓ₂} → Bot {ℓ₁} → A
absurd ()
