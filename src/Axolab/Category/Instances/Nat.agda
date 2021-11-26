
module Axolab.Category.Instances.Nat where

open import Axolab.Category
open import Axolab.Category.Instances.Nat.Core
open import Axolab.Prelude

open Category

-- ---------------------------------------------------------------------------------------------------------------------

-- The category of natural numbers under their usual ordering. We use ℕ to refer to the objects of Nat.
--
Nat : Category 0ℓ 0ℓ
Ob     Nat = ℕ
Hom    Nat = _≤_
id     Nat = ≤-refl
_∘_    Nat = ≤-trans
id←    Nat = ≤-id← _
id→    Nat = ≤-id⇢ _
assoc← Nat = ≤-assoc← _ _ _
assoc→ Nat = sym (≤-assoc← _ _ _)
