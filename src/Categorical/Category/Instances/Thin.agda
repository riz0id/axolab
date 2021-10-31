
module Categorical.Category.Instances.Thin where

open import Categorical.Category
open import Prelude
open import Prelude.Data.Coproduct
open import Relation.Structure.Poset

open Category

-- ---------------------------------------------------------------------------------------------------------------------

module _  {o ℓ} {U : Setoid o} (poset : Poset U ℓ) where
  open Poset poset

  Thin : Category o ℓ
  Ob     Thin = U
  Hom    Thin = _≤_
  id     Thin = refl≤
  _∘_    Thin = λ y x → trans≤ x y
  id←    Thin = const≤← _
  id→    Thin = const≤→ _
  assoc← Thin = assoc≤← _ _ _
  assoc→ Thin = assoc≤→ _ _ _
