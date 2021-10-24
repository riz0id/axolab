module Categorical.Category.Instances.Sets where

open import Categorical.Category
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

open Category

Sets : (o : Level) → Category (lsuc o) o
Ob     (Sets o) = Setoid o
Hom    (Sets o) = λ A B → A → B
id     (Sets o) = λ X → X
_∘_    (Sets o) = λ f g x → f (g x)
id←    (Sets o) = λ f → refl
id→    (Sets o) = λ f → refl
assoc← (Sets o) = λ f g h → refl
assoc→ (Sets o) = λ f g h → refl
