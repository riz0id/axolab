
module Categorical.Category.Instances.Functors where

open import Categorical.Category
open import Categorical.Functor
open import Categorical.NaturalTransformation
open import Prelude

open Category

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ : Level

-- ---------------------------------------------------------------------------------------------------------------------

Functors : Category o₁ ℓ₁ → Category o₂ ℓ₂ → Category (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂)
Ob     (Functors C D) = Functor C D
Hom    (Functors C D) = NaturalTransformation
id     (Functors C D) = idNT
_∘_    (Functors C D) = _∘⇑_
id←    (Functors C D) = id-η←
id→    (Functors C D) = id-η→
assoc← (Functors C D) {f = f} {g = g} = assoc-η← {α = f} {β = g}
assoc→ (Functors C D) {f = f} {g = g} = assoc-η→ {α = f} {β = g}
