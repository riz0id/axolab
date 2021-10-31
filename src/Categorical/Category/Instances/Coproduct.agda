
module Categorical.Category.Instances.Coproduct where

open import Categorical.Category
open import Prelude
open import Prelude.Data.Coproduct

open Category

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ : Level

-- ---------------------------------------------------------------------------------------------------------------------

_+Cat_ : Category o₁ ℓ₁ → Category o₂ ℓ₂ → Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂)
Ob (C +Cat D) = Ob C ∐ Ob D
Hom (C +Cat D) f g = {!!} ∐ {!!}
id (C +Cat D) = {!!}
_∘_ (C +Cat D) = {!!}
id← (C +Cat D) = {!!}
id→ (C +Cat D) = {!!}
assoc← (C +Cat D) = {!!}
assoc→ (C +Cat D) = {!!}
