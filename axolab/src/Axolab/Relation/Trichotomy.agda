
module Axolab.Relation.Trichotomy where

open import Axolab.Prelude
open import Axolab.Relation.Negation

private
  variable
    a b c : Level

-- ---------------------------------------------------------------------------------------------------------------------

data Trichotomy (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where
  tri< :   A → ¬ B → ¬ C → Trichotomy A B C
  tri≈ : ¬ A →   B → ¬ C → Trichotomy A B C
  tri> : ¬ A → ¬ B →   C → Trichotomy A B C
