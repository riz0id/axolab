
module Axolab.Data.Vec.Core where

open import Axolab.Data.Fin
open import Axolab.Data.Nat
open import Axolab.Prelude

infixr 40 _∷_

-- ---------------------------------------------------------------------------------------------------------------------

data Vec {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  nil : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (1 + n)
