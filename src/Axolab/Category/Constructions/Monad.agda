
open import Axolab.Category

module Axolab.Category.Constructions.Monad {o ℓ} (C : Category o ℓ) where

open import Axolab.Category.Functor
open import Axolab.Category.NaturalTransformation
open import Axolab.Prelude

open Category C
open Functor

-- ---------------------------------------------------------------------------------------------------------------------

record Monad : Setoid (o ⊔ ℓ) where
  field
    M    : Endofunctor C
    unit : Id ⇒ M
    mult : (M F∘ M) ⇒ M

  module unit = NaturalTransformation unit
  module mult = NaturalTransformation mult

  M₀   = F₀   M
  M₁   = F₁   M
  M-id = F-id M
  M-∘  = F-∘  M

  field
    ident← : {X : Ob} → mult.η X ∘ M₁ (unit.η X) ≡ id
    ident→ : {X : Ob} → mult.η X ∘ unit.η (M₀ X) ≡ id
    assoc  : {X : Ob} → mult.η X ∘ M₁ (mult.η X) ≡ mult.η X ∘ mult.η (M₀ X)
