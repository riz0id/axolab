
module Axolab.Category.Instances.Product where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Data.Product
open import Axolab.Prelude

open Category

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ o₄ ℓ₄ : Level

    C₁ : Category o₁ ℓ₁
    C₂ : Category o₃ ℓ₃
    D₁ : Category o₂ ℓ₂
    D₂ : Category o₄ ℓ₄

-- ---------------------------------------------------------------------------------------------------------------------

infixr 6 _×Cat_

_×Cat_ : {o₁ ℓ₁ o₂ ℓ₂ : Level} → Category o₁ ℓ₁ → Category o₂ ℓ₂ → Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂)
Ob     (C ×Cat D)                 = Ob C × Ob D
Hom    (C ×Cat D) (X , Z) (Y , W) = Hom C X Y × Hom D Z W
id     (C ×Cat D)                 = id C , id D
_∘_    (C ×Cat D) (f , h) (g , i) = _∘_ C f g , _∘_ D h i
id←    (C ×Cat D)                 = ×Path (id← C) (id← D)
id→    (C ×Cat D)                 = ×Path (id→ C) (id→ D)
assoc← (C ×Cat D)                 = ×Path (assoc← C) (assoc← D)
assoc→ (C ×Cat D)                 = ×Path (assoc→ C) (assoc→ D)

-- _×F_ : (F : Functor C₁ D₁) (G : Functor C₂ D₂) → Functor (C₁ ×Cat C₂) (D₁ ×Cat D₂)
-- _×F_ {D₁ = D₁} F G =
--   record { F₀   = λ where (A , B) → F.₀ A , G.₀ B
--          ; F₁   = λ where (f , g) → F.₁ f , G.₁ g
--          ; F-id = ×Path (subst (_≡ id D₁) {!!} {!!}) {!!}
--          ; F-∘  = λ where (f , g) (h , i) → {!!}
--          }
--   where
--     module F = Functor F
--     module G = Functor G
