
open import Prelude
open import Relation.Structure.Poset

module Topos.Instances.Temporal.Glue {o ℓ ℓ'} {T : Setoid o} (poset : Poset T ℓ ℓ') where

open import Prelude.Equality
open import Topos.Instances.Temporal.Interval poset

open Poset poset

private
  variable
    𝑖 𝑖₁ 𝑖₂ 𝑖₃ : Interval

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _∪_

record Glue (𝑖 𝑖' : Interval) : Setoid (o ⊔ ℓ) where
  constructor glue

  module 𝑖  = Interval 𝑖
  module 𝑖' = Interval 𝑖'
  field
    point    : 𝑖.ₜ ≡ 𝑖'.ₜ
    restrict : 𝑖.ₒ ≤ 𝑖'.ₒ

glueId : Glue 𝑖 𝑖
glueId = glue refl refl≤

_∪_ : Glue 𝑖₁ 𝑖₂ → Glue 𝑖₂ 𝑖₃ → Glue 𝑖₁ 𝑖₃
glue p₁ r₁ ∪ glue p₂ r₂ = glue (p₁ ∘p p₂) (trans≤ r₁ r₂)
