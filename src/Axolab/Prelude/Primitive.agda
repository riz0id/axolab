{-# OPTIONS --safe #-}

module Axolab.Prelude.Primitive where

-- ---------------------------------------------------------------------------------------------------------------------

open import Agda.Primitive public
  using    ( Level; lsuc; lzero; _⊔_ )
  renaming ( Set to Setoid; Setω to Setoidω )

record Lift {ℓ ℓ' : _} (A : Setoid ℓ) : Setoid (ℓ ⊔ ℓ') where
  constructor lift
  field
    unlift : A

open Lift public

0ℓ : Level
0ℓ = lzero

1ℓ : Level
1ℓ = lsuc lzero
