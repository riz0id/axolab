
module Axolab.Prelude.Primitive.Fin where

open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude.Primitive

-- ---------------------------------------------------------------------------------------------------------------------

data Fin : Nat → Setoid where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} (i : Fin n) → Fin (suc n)

fromNat : (n : Nat) → Fin (suc n)
fromNat zero    = fzero
fromNat (suc n) = fsuc (fromNat n)
