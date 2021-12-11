
module Axolab.Category.Functor.Core where

open import Axolab.Category
open import Axolab.Prelude

private
  variable
    o ℓ o' ℓ' : Level
    C : Category o ℓ
    D : Category o' ℓ'

-- ---------------------------------------------------------------------------------------------------------------------

record Functor (C : Category o ℓ) (D : Category o' ℓ') : Set (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  private module C = Category C
  private module D = Category D

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

open Functor

Endofunctor : (C : Category o ℓ) → Set (o ⊔ ℓ)
Endofunctor C = Functor C C

Id : Functor C C
F₀   Id x   = x
F₁   Id f   = f
F-id Id     = refl
F-∘  Id _ _ = refl

Op : Functor C D → Functor (C ^op) (D ^op)
F₀   (Op F) = F₀ F
F₁   (Op F) = F₁ F
F-id (Op F) = F-id F
F-∘  (Op F) = λ f g → F-∘ F g f
