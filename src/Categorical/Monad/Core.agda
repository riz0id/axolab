
open import Categorical.Category

module Categorical.Monad.Core {o ℓ} (C : Category o ℓ) where

open import Categorical.Functor
open import Categorical.NaturalTransformation
open import Prelude
open import Prelude.Equality

open Category C

private
  variable
    X Y Z : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Monad : Setoid (o ⊔ ℓ) where
  field
    M    : Endofunctor C
    unit : NaturalTransformation Id M
    mult : NaturalTransformation (M F∘ M) M

  module unit = NaturalTransformation unit
  module mult = NaturalTransformation mult

  open module M = Functor M
    renaming ( F₀ to M₀; F₁ to M₁; F-id to M-id; F-∘ to M-∘ )

  field
    identity← : mult.η X ∘ M₁ (unit.η X) ≡ id
    identity→ : mult.η X ∘ unit.η (M₀ X) ≡ id
    M-assoc   : mult.η X ∘ M₁ (mult.η X) ≡ mult.η X ∘ mult.η (M₀ X)
