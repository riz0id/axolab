
open import Axolab.Category

module Axolab.Category.Monad.Core {o ℓ} (C : Category o ℓ) where

open import Axolab.Category.Functor
open import Axolab.Category.NaturalTransformation
open import Axolab.Prelude

open Category C

private
  module Id = Functor (Id {C = C})

-- ---------------------------------------------------------------------------------------------------------------------

record Monad : Setoid (o ⊔ ℓ) where
  field
    M    : Endofunctor C
    unit : Id ⇒ M
    mult : (M F∘ M) ⇒ M

  open module M = Functor M public
    renaming ( F₀ to M₀; F₁ to M₁; F-id to M-id; F-∘ to M-∘ )

  open module unit = NaturalTransformation unit public
    using    ( η )
    renaming ( natural to η-commutes )

  open module mult = NaturalTransformation mult public
    using    ( )
    renaming ( η to μ; natural to μ-commutes )

  field
    ident← : {X : Ob} → μ X ∘ M₁ (η X) ≡ id
    ident→ : {X : Ob} → μ X ∘ η (M₀ X) ≡ id
    assoc  : {X : Ob} → μ X ∘ M₁ (μ X) ≡ μ X ∘ μ (M₀ X)
