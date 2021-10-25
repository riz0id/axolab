
open import Prelude
open import Relation.Structure.Poset

module Topos.Instances.Temporal.TemporalIndex
  {o ℓ ℓ'} {T : Setoid o}
  (poset : Poset T ℓ ℓ')
  where

open import Categorical.Category
open import Prelude.Equality
open import Topos.Instances.Temporal.Interval poset
open import Topos.Instances.Temporal.Glue poset

open Category
open Poset poset

-- ---------------------------------------------------------------------------------------------------------------------

TemporalIndex : Category (o ⊔ ℓ) (o ⊔ ℓ)
Ob     TemporalIndex = Interval
Hom    TemporalIndex = Glue
id     TemporalIndex = glueId
_∘_    TemporalIndex = λ g₁ g₂ → g₂ ∪ g₁
id←    TemporalIndex = ap₂ glue (UIP _ _) (const≤← _)
id→    TemporalIndex = ap₂ glue (UIP _ _) (const≤→ _)
assoc← TemporalIndex = ap₂ glue (UIP _ _) (assoc≤← _ _ _)
assoc→ TemporalIndex = ap₂ glue (UIP _ _) (assoc≤→ _ _ _)
