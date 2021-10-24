
module Prelude.Data.Unit where

open import Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record Top {ℓ} : Setoid ℓ where
  instance constructor tt

{-# BUILTIN UNIT Top #-}
