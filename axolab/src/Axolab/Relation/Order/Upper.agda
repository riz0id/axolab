
open import Axolab.Relation.Structure.Poset

module Axolab.Relation.Order.Upper
  {o ℓ} {A : Set o}
  (poset : Poset A ℓ)
  where

open import Axolab.Prelude

open module poset = Poset poset

-- --------------------------------------------------------------------------------------------------------------------

record _↑ (x : A) : Set (o ⊔ ℓ) where
  eta-equality
  constructor [_]↑

  field
    point : A
    proof : x ≤ point
