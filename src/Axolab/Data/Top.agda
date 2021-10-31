
module Axolab.Data.Top where

open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record Top {ℓ} : Setoid ℓ where
  instance constructor tt

{-# BUILTIN UNIT Top #-}
