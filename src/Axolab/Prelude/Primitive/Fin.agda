
module Axolab.Prelude.Primitive.Fin where

open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude.Primitive

-- ---------------------------------------------------------------------------------------------------------------------

data Fin : ℕ → Setoid where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} (i : Fin n) → Fin (suc n)

fromNat : (n : ℕ) → Fin (suc n)
fromNat zero    = fzero
fromNat (suc n) = fsuc (fromNat n)
