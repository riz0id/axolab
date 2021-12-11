
module Axolab.Algebra.Theory.Term where

open import Axolab.Data.Fin
open import Axolab.Data.Nat
open import Axolab.Data.Vec as Vec
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

Signature : (ℓ : Level) → Set (lsuc ℓ)
Signature ℓ = @0 ℕ → Set ℓ

Laws : (ℓ : Level) → Set (lsuc ℓ)
Laws ℓ = @0 ℕ → Set ℓ

data Term {ℓ} (S : Signature ℓ) : @0 ℕ → Set ℓ where
  var  : {n   : ℕ} → Fin n → Term S n
  term : {m n : ℕ} → S m → Vec (Term S n) m → Term S n
