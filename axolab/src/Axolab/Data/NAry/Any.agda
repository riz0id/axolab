
module Axolab.Data.NAry.Any where

open import Axolab.Data.List
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------



data Any {ℓ ℓ'} {A : Setoid ℓ} (P : A → Setoid ℓ') : List A → Setoid (ℓ ⊔ ℓ') where
  here  : ∀ {x xs} → P x → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)
