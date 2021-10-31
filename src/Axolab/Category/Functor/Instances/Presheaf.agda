
module Axolab.Category.Functor.Instances.Presheaf where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Category.Instances.Set
open import Axolab.Prelude

open Category
open Functor

-- ---------------------------------------------------------------------------------------------------------------------

Presheaf : ∀ {o ℓ} (C : Category o ℓ) (ℓ' : Level) → Setoid (o ⊔ ℓ ⊔ lsuc ℓ')
Presheaf C ℓ' = Functor (C ^op) (Set ℓ')
