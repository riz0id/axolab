
module Axolab.Data.Fin where

open import Axolab.Data.Nat.Core
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

data Fin : ℕ → Setoid where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)
