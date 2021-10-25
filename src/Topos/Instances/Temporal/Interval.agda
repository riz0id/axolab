
open import Prelude
open import Relation.Structure.Poset

module Topos.Instances.Temporal.Interval {o ℓ ℓ'} {T : Setoid o} (poset : Poset T ℓ ℓ') where

open Poset poset

-- ---------------------------------------------------------------------------------------------------------------------

record Interval : Setoid (o ⊔ ℓ) where
  constructor [_×_∣_]
  field
    inhabit  : T
    observe  : T
    restrict : inhabit ≤ observe

  -- Subscript "t" for "inhabit time"
  ₜ : T
  ₜ = inhabit

  -- Subscript "o" shorthand for "observed time"
  ₒ : T
  ₒ = observe
