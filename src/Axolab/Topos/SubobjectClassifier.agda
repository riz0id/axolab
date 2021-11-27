
open import Axolab.Category.Bundle.CartesianCategory

module Axolab.Topos.SubobjectClassifier {o ℓ} (Ca : CartesianCategory o ℓ) where

open import Axolab.Category
open import Axolab.Prelude

import Axolab.Category.Morphism
import Axolab.Category.Diagram.Pullback

private
  open module Ca = CartesianCategory Ca

open Axolab.Category.Morphism         U
open Axolab.Category.Diagram.Pullback U
open Monomorphism

-- ---------------------------------------------------------------------------------------------------------------------

record SubobjectClassifier : Set (o ⊔ ℓ) where
  field
    Ω    : Ob
    true : Hom ⊤ Ω
    χ    : {U X : Ob} → U ↪ X → Hom X Ω

  field
    pullback : {U X : Ob} → (h : U ↪ X) → Pullback ! (into h) true (χ h)
