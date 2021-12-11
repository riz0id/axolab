
module Axolab.Type.Bot where

open import Axolab.Type

-- ---------------------------------------------------------------------------------------------------------------------

data ⊥ : Type where

absurd : ∀ {ℓ} {A : Type ℓ} → ⊥ → A
absurd ()
