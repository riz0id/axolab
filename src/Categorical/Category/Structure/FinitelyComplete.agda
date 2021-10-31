
open import Categorical.Category

module Categorical.Category.Structure.FinitelyComplete {o ℓ} (C : Category o ℓ) where

open import Categorical.Diagram.Equalizer C
open import Categorical.Diagram.Pullback C
open import Prelude
open import Prelude.Equality

open Category C

private
  variable
    X Y Z : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record FinitelyComplete : Setoid (o ⊔ ℓ) where
  field
    Pullback-of : (f : Hom X Z) (g : Hom Y Z) → Ob
    pb-π₁       : {f : Hom X Z} {g : Hom Y Z} → Hom (Pullback-of f g) X
    pb-π₂       : {f : Hom X Z} {g : Hom Y Z} → Hom (Pullback-of f g) Y
    is-pullback : (f : Hom X Z) (g : Hom Y Z) → Pullback (pb-π₁ {f = f} {g = g}) pb-π₂ f g

  field
    Equalizer-of : (f g : Hom X Y) → Ob
    equalize     : (f g : Hom X Y) → Hom (Equalizer-of f g) X
    is-equalizer : (f g : Hom X Y) → Equalizer f g (equalize f g)
