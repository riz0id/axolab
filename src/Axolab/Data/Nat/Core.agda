
module Axolab.Data.Nat.Core where

open import Axolab.Prelude
open import Axolab.Prelude.Primitive.Nat public

infix 6 _≤_

-- ---------------------------------------------------------------------------------------------------------------------

data _≤_ : ℕ → ℕ → Setoid where
  ≤-zero : {n   : ℕ} → 0 ≤ n
  ≤-suc  : {m n : ℕ} → m ≤ n → suc m ≤ suc n
