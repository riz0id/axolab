module Categorical.Bifunctor.Core where

open import Categorical.Category
open import Categorical.Category.Instances.Product
open import Categorical.Functor
open import Prelude
open import Prelude.Data.Product
open import Prelude.Equality

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level

-- ---------------------------------------------------------------------------------------------------------------------

module _ (C : Category o₁ ℓ₁) (D : Category o₂ ℓ₂) (E : Category o₃ ℓ₃) where
  private
    module C = Category C
    module D = Category D
    module E = Category E

  Bifunctor : Setoid (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ o₃ ⊔ ℓ₃)
  Bifunctor = Functor (C ×Cat D) E


module _ {C : Category o₁ ℓ₁} {D : Category o₂ ℓ₂} {E : Category o₃ ℓ₃} (F : Bifunctor C D E) where
  open PropReasoning

  private
    module C = Category C
    module D = Category D
    module E = Category E

    open module F = Functor F

  biap : C.Ob → D.Ob → E.Ob
  biap A B = F₀ (A , B)

  first : {A B : C.Ob} {X : D.Ob} → C.Hom A B → E.Hom (F₀ (A , X)) (F₀ (B , X))
  first f = F₁ (f , D.id)

  second : {A B : D.Ob} {X : C.Ob} → D.Hom A B → E.Hom (F₀ (X , A)) (F₀ (X , B))
  second f = F₁ (C.id , f)

  Left : D.Ob → Functor C E
  F₀   (Left Y) X   = F₀ (X , Y)
  F₁   (Left Y) f   = first f
  F-id (Left Y)     = F-id
  F-∘  (Left Y) f g =
    first (f C.∘ g)              ≡⟨ sym (ap (λ e → F₁ (f C.∘ g , e)) D.id←) ⟩
    F₁ (f C.∘ g , D.id D.∘ D.id) ≡⟨ F-∘ _ _ ⟩
    first f E.∘ first g          ∎

  Right : C.Ob → Functor D E
  F₀   (Right X) Y   = F₀ (X , Y)
  F₁   (Right X) f   = second f
  F-id (Right X)     = F-id
  F-∘  (Right X) f g =
    second (f D.∘ g)             ≡⟨ sym (ap (λ e → F₁ (e , f D.∘ g)) C.id←) ⟩
    F₁ (C.id C.∘ C.id , f D.∘ g) ≡⟨ F-∘ _ _ ⟩
    second f E.∘ second g        ∎
