module Categorical.NaturalTransformation.Core where

open import Categorical.Category
open import Categorical.Functor
open import Prelude
open import Prelude.Equality

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o ℓ o' ℓ'} {C : Category o ℓ} {D : Category o' ℓ'} where
  private
    module C = Category C
    module D = Category D

  record NaturalTransformation (F G : Functor C D) : Setoid (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    private
      module F = Functor F
      module G = Functor G

    field
      η       : (X : C.Ob) → D.Hom (F.₀ X) (G.₀ X)
      natural : (X Y : C.Ob) (f : C.Hom X Y) → η Y D.∘ F.₁ f ≡ G.₁ f D.∘ η X
