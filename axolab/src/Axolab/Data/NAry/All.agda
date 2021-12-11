
module Axolab.Data.NAry.All where

open import Axolab.Data.List
open import Axolab.Prelude

infixr 5 _∷_

-- ---------------------------------------------------------------------------------------------------------------------

data All {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') : List A → Set (ℓ ⊔ ℓ') where
  nil : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)
