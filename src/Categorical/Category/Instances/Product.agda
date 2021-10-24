module Categorical.Category.Instances.Product where

open import Categorical.Category
open import Prelude
open import Prelude.Data.Product

-- ---------------------------------------------------------------------------------------------------------------------

open Category

_×Cat_ : {o₁ ℓ₁ o₂ ℓ₂ : Level} → Category o₁ ℓ₁ → Category o₂ ℓ₂ → Category (o₁ ⊔ o₂) (ℓ₁ ⊔ ℓ₂)
Ob     (C ×Cat D)                 = Ob C × Ob D
Hom    (C ×Cat D) (X , Z) (Y , W) = Hom C X Y × Hom D Z W
id     (C ×Cat D)                 = id C , id D
_∘_    (C ×Cat D) (f , h) (g , i) = _∘_ C f g , _∘_ D h i
id←    (C ×Cat D) (f , g)         = ×Path (id← C f) (id← D g)
id→    (C ×Cat D) (f , g)         = ×Path (id→ C f) (id→ D g)
assoc← (C ×Cat D) f g h           = ×Path (assoc← C _ _ _) (assoc← D _ _ _)
assoc→ (C ×Cat D) f g h           = ×Path (assoc→ C _ _ _) (assoc→ D _ _ _)
