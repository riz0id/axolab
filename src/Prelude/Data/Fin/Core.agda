{-# OPTIONS --safe #-}

module Prelude.Data.Fin.Core where

open import Prelude.Data.Nat
open import Prelude.Primitive

-- ---------------------------------------------------------------------------------------------------------------------

data Fin : ℕ → Setoid where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)
