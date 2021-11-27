{-# OPTIONS --safe #-}

module Axolab.Prelude.Primitive where

open import Agda.Primitive public

-- ---------------------------------------------------------------------------------------------------------------------

record Lift {ℓ ℓ' : _} (A : Set ℓ) : Set (ℓ ⊔ ℓ') where
  constructor lift
  field
    unlift : A

open Lift public

0ℓ : Level
0ℓ = lzero

1ℓ : Level
1ℓ = lsuc lzero
