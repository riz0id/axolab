
module Axolab.Category.Instances.Nat where

open import Axolab.Category
open import Axolab.Category.Constructions.Thin
open import Axolab.Data.Nat.Properties
open import Axolab.Prelude

open Category

-- ---------------------------------------------------------------------------------------------------------------------

-- The category of natural numbers under their usual ordering. We use ℕ to refer to the objects of Nat.
--
Nat : Category 0ℓ 0ℓ
Nat = Thin ℕ-poset
