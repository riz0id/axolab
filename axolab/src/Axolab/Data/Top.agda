
module Axolab.Data.Top where

open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record Top {ℓ} : Set ℓ where
  instance constructor tt

{-# BUILTIN UNIT Top #-}

⊤ : Set
⊤ = Top
