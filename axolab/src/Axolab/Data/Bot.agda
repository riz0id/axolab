
module Axolab.Data.Bot where

open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

data Bot {ℓ} : Set ℓ where

⊥ : Set
⊥ = Bot

absurd : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₂} → Bot {ℓ₁} → A
absurd ()
