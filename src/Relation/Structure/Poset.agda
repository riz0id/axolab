
open import Prelude

module Relation.Structure.Poset {o} (U : Setoid o) where

open import Relation.Structure.Equivalence
open import Relation.Structure.Proset
open import Prelude.Equality

private
  variable
    A B C : U

-- ---------------------------------------------------------------------------------------------------------------------

record Poset (ℓ ℓ' : Level) : Setoid (lsuc (o ⊔ ℓ ⊔ ℓ')) where
  field
    proset : Proset U ℓ ℓ'

  open module proset = Proset proset public

  field
    antisym : A ≤ B → B ≤ A → A ≡ B
