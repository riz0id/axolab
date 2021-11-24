
open import Categorical.Category.Bundle.Cartesian

module Topos.SubobjectClassifier {o ℓ} (Ca : CartesianCategory o ℓ) where

open import Categorical.Category
open import Prelude

import Categorical.Morphism
import Categorical.Diagram.Pullback

-- ---------------------------------------------------------------------------------------------------------------------

record SubobjectClassifier : Setoid (o ⊔ ℓ) where
  private
    open module Ca = CartesianCategory Ca

    open Categorical.Morphism         U
    open Categorical.Diagram.Pullback U

    open Monomorphism

  field
    Ω    : Ob
    true : Hom ⊤ Ω
    χ    : {U X : Ob} → U ↪ X → Hom X Ω

  field
    pullback : {U X : Ob} → (h : U ↪ X) → Pullback ! (into h) true (χ h)
