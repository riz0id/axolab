
module Axolab.Category.Instances.Cat.Core where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Prelude

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
