module Categorical.Functor.Core where

open import Categorical.Category
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

record Functor {o ℓ o' ℓ'} (C : Category o ℓ) (D : Category o' ℓ') : Setoid (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  private
    module C = Category C
    module D = Category D

  field
    F₀ : C.Ob → D.Ob
    F₁ : {X Y : C.Ob} → C.Hom X Y → D.Hom (F₀ X) (F₀ Y)

  field
    F-id : {X : C.Ob} → F₁ C.id ≡ D.id {F₀ X}
    F-∘  : {X Y Z : C.Ob} (g : C.Hom Y Z) (f : C.Hom X Y) → F₁ (g C.∘ f) ≡ F₁ g D.∘ F₁ f

  ₀ : C.Ob → D.Ob
  ₀ = F₀

  ₁ : {X Y : C.Ob} → C.Hom X Y → D.Hom (F₀ X) (F₀ Y)
  ₁ = F₁
