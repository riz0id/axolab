
module Axolab.Category.Functor.Adjoint where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Category.NaturalTransformation
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o₁ ℓ₁ o₂ ℓ₂} {C : Category o₁ ℓ₁} {D : Category o₂ ℓ₂} where
  private
    module C = Category C
    module D = Category D

  infixr 4 Adjoint

  syntax Adjoint F G = F ⊣ G

  record Adjoint (F : Functor C D) (G : Functor D C) : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
    private
      module F = Functor F
      module G = Functor G

    field
      unit   : NaturalTransformation Id (G F∘ F)
      counit : NaturalTransformation (F F∘ G) Id

    module unit   = NaturalTransformation unit
    module counit = NaturalTransformation counit

    field
      zip : {X : C.Ob} → counit.η (F.₀ X) D.∘ F.₁ (unit.η X) ≡ D.id
      zag : {Y : D.Ob} → G.₁ (counit.η Y) C.∘ unit.η (G.₀ Y) ≡ C.id
