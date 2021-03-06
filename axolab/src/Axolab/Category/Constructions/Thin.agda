
open import Axolab.Prelude
open import Axolab.Relation.Structure.Proset

module Axolab.Category.Constructions.Thin
  {o ℓ} {A : Set o}
  (proset : Proset A ℓ)
  where

open import Axolab.Category

open Category
open Proset proset

-- ---------------------------------------------------------------------------------------------------------------------

Thin : Category o ℓ
Ob     Thin = A
Hom    Thin = _~_
id     Thin = refl~
_∘_    Thin = λ g f → trans~ f g
id←    Thin = id~/← _
id→    Thin = id~/→ _
assoc← Thin = assoc~/→ _ _ _
assoc→ Thin = assoc~/← _ _ _
