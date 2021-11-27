
open import Axolab.Category
open import Axolab.Category.Structure.Cartesian

module Axolab.Algebra.Iterative.Core
  {o ℓ} {C : Category o ℓ}
  (Ca : Cartesian (C ^op))
  where

open import Axolab.Category.Functor
open import Axolab.Prelude

open Cartesian Ca
  renaming ( _×₀_ to _+₀_; _×₁_ to _+₁_
           ; -×- to -+-; _×- to _+-; -×_ to -+_
           ; ⊤ to ⊥; π₁ to inj₁; π₂ to inj₂
           ; π₁×π₂≡id to inj₁+inj₂≡id; π₁×₁≡id to +₁inj₁≡id; π₂×₁≡id to +₁inj₂≡id
           ; ×₁-distrib to +₁-distrib )
open Category C

private
  variable
    X A : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record FlatEquation (H : Endofunctor C) : Set (o ⊔ ℓ) where
  private
    module H = Functor H

  field
    equation : Hom X (H.₀ X +₀ A)

record Solution (H : Endofunctor C) : Set (o ⊔ ℓ) where
  private
    module H = Functor H

  field
    equation : Hom X (H.₀ X +₀ A)
    algebra  : Hom (H.₀ X) X
    solution : Hom X A

  field
    solves : solution ≡ (algebra ∘ solution +₁ id) ∘ equation
