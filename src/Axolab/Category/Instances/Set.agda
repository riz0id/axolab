
module Axolab.Category.Instances.Set where

open import Axolab.Category
open import Axolab.Prelude

open Category

-- ---------------------------------------------------------------------------------------------------------------------

Set : (o : Level) → Category (lsuc o) o
Ob     (Set o)       = Setoid o
Hom    (Set o) A B   = A → B
id     (Set o) A     = A
_∘_    (Set o) g f A = g (f A)
id←    (Set o)       = refl
id→    (Set o)       = refl
assoc← (Set o)       = refl
assoc→ (Set o)       = refl
