module Axolab.Category.Instances.BinTree where

open import Axolab.Category
open import Axolab.Data.BinTree
open import Axolab.Prelude

open Category

-- ---------------------------------------------------------------------------------------------------------------------

BinTrees : {ℓ : Level} → Set ℓ → Category ℓ (lsuc ℓ)
Ob     (BinTrees U) = Tree U
Hom    (BinTrees U) = Homomorphism
id     (BinTrees U) = IdHomo
_∘_    (BinTrees U) = _∘H_
id←    (BinTrees U) = Homomorphism≡ refl
id→    (BinTrees U) = Homomorphism≡ refl
assoc← (BinTrees U) = Homomorphism≡ refl
assoc→ (BinTrees U) = Homomorphism≡ refl
