
module Axolab.Algebra.Theory.Signature where

open import Axolab.Data.Nat.Core
open import Axolab.Data.Vect
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record Signature (ℓ : Level) : Setoid (lsuc ℓ) where
  field
    operations : Setoid ℓ
    o-arities  : operations → ℕ

open Signature

Interprets : ∀ {ℓ ℓ'} (A : Setoid ℓ) (S : Signature ℓ') → Setoid (ℓ ⊔ ℓ')
Interprets A S = (o : operations S) → Vect A (o-arities S o) → A
