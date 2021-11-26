
module Axolab.Category.Instances.FinSet where

open import Axolab.Category
open import Axolab.Category.Instances.Functors
open import Axolab.Category.Instances.Nat
open import Axolab.Category.Instances.Set
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

FinSet : (o : Level) → Category (lsuc o) (lsuc o)
FinSet o = Functors Nat (Set o)

