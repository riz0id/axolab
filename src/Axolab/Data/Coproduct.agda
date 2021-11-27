
module Axolab.Data.Coproduct where

open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _∐_

data _∐_ {ℓ ℓ' : _} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  left  : A → A ∐ B
  right : B → A ∐ B

open _∐_ public
