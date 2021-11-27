

module Axolab.Category.Functor.Structure.Monoidal where

open import Axolab.Category
open import Axolab.Category.Bundle.MonoidalCategory
open import Axolab.Category.Functor
open import Axolab.Category.NaturalTransformation
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o ℓ o' ℓ'} {C : MonoidalCategory o ℓ} {D : MonoidalCategory o' ℓ'} where
  private
    module C = MonoidalCategory C
    module D = MonoidalCategory D

  record MonoidalFunctor (F : Functor C.U D.U) : Set (o ⊔ ℓ ⊔ o ⊔ ℓ') where
    eta-equality
    private module F = Functor F

    field
      ε      : D.Hom D.unit (F.₀ C.unit)
      ⨂-homo : NaturalTransformation (D.⨂ F∘ {!!}) {!!}
