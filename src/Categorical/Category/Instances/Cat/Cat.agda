
module Categorical.Category.Instances.Cat.Cat where

open import Categorical.Category
open import Categorical.Functor
open import Prelude
open import Prelude.Equality

open Category

-- ---------------------------------------------------------------------------------------------------------------------

Cat : (o ℓ : Level) → Category (lsuc (o ⊔ ℓ)) (o ⊔ ℓ)
Ob     (Cat o ℓ) = Category o ℓ
Hom    (Cat o ℓ) = Functor
id     (Cat o ℓ) = Id
_∘_    (Cat o ℓ) = _F∘_
id←    (Cat o ℓ) = Functor≡ refl λ _ → refl
id→    (Cat o ℓ) = Functor≡ refl λ _ → refl
assoc← (Cat o ℓ) = Functor≡ refl λ _ → refl
assoc→ (Cat o ℓ) = Functor≡ refl λ _ → refl
