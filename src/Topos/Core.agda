
open import Categorical.Category

module Topos.Core {o ℓ} (C : Category o ℓ) where

open import Categorical.Category.Bundle.Cartesian
open import Categorical.Category.Structure.Cartesian
open import Categorical.Category.Structure.CartesianClosed
open import Categorical.Category.Structure.Cocartesian
open import Categorical.Category.Structure.FinitelyComplete
open import Topos.SubobjectClassifier
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

record ElementaryTopos : Setoid (lsuc (o ⊔ ℓ)) where
  field
    cartesian        : Cartesian C
    finitelyComplete : FinitelyComplete C
    closed           : CartesianClosed C cartesian

  cartesianCategory : CartesianCategory o ℓ
  cartesianCategory = record { U = C ; ca = cartesian }

  field
    subobjectClassifier : SubobjectClassifier cartesianCategory
    cocartesian         : Cartesian (C ^op)

  open Cartesian           cartesian           public
  open CartesianClosed     closed              public
  open SubobjectClassifier subobjectClassifier public
  open FinitelyComplete    finitelyComplete    public
  open Category            C                   public

  open Cartesian cocartesian public
    using    ( )
    renaming ( π₁          to inj₁
             ; π₂          to inj₂
             ; _×₁_        to case
             ; _×₀_        to _+₀_
             ; ×-unique    to case-unique
             ; π₁×₁≡id     to case∘inj₁≡id
             ; π₂×₁≡id     to case∘inj₂≡id
             ; ⊤           to ⊥
             ; ⊤-terminal  to ⊥-initial
             ; terminal    to initial
             ; !           to absurd
             ; ×-unique₂   to case-unique₂
             )
