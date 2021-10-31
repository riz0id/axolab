-- Concrete process categories
--

open import Categorical.Category

module Categorical.Category.Instances.CCCC {o ℓ} (C : Category o ℓ) where

open import Categorical.Category.Structure.Cartesian       C
open import Categorical.Category.Structure.CartesianClosed C
open import Categorical.Object.Coproduct                   C
open import Prelude

open Category C

-- ---------------------------------------------------------------------------------------------------------------------

record CCCC : Setoid (o ⊔ ℓ) where
  field
    cartesian  : Cartesian
    closed     : CartesianClosed cartesian
    coproducts : (A B : Ob) → Coproduct A B

  open module cartesian = Cartesian cartesian public

  _+₀_ : Ob → Ob → Ob
  A +₀ B = Coproduct.A+B (coproducts A B)

  _+₁_ : {A B X : Ob} → Hom A X → Hom B X → Hom (A +₀ B) X
  f +₁ g = Coproduct.[_,_] (coproducts _ _) f g
