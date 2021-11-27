
module Axolab.Data.Fin.Core where

open import Axolab.Data.Nat
open import Axolab.Data.Top
open import Axolab.Data.Bot
open import Axolab.Prelude
open import Agda.Builtin.FromNat

-- ---------------------------------------------------------------------------------------------------------------------

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} (i : Fin n) → Fin (suc n)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero    = fzero
fromℕ (suc n) = fsuc (fromℕ n)

fromℕ< : ∀ {m n} → m < n → Fin n
fromℕ< {zero}  {suc n} m<n = fzero
fromℕ< {suc m} {suc n} m<n = fsuc (fromℕ< (≤-pred m<n))
