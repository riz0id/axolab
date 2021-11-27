
module Axolab.Data.Nat.Properties where

open import Axolab.Data.Nat as ℕ
open import Axolab.Prelude
open import Axolab.Relation.Structure.Proset ℕ
open import Axolab.Relation.Structure.Poset ℕ

open Proset
open Poset

-- ---------------------------------------------------------------------------------------------------------------------

ℕ-proset : Proset 0ℓ
_~_        ℕ-proset = ℕ._≤_
reflexive~ ℕ-proset {zero}  = λ where
  refl → ≤-zero
reflexive~ ℕ-proset {suc _} = λ where
  refl → ≤-suc (reflexive~ ℕ-proset refl)
trans~     ℕ-proset =
  λ { ≤-zero      → λ _ → ≤-zero
    ; (≤-suc m≤n) → λ where
      (≤-suc n≤o) → ≤-suc (trans~ ℕ-proset m≤n n≤o) }
isProp~    ℕ-proset =
  λ { ≤-zero      ≤-zero       → refl
    ; (≤-suc m≤n) (≤-suc m≤n') → ap ≤-suc (isProp~ ℕ-proset m≤n m≤n') }

ℕ-poset : Poset 0ℓ
proset   ℕ-poset = ℕ-proset
antisym≤ ℕ-poset =
  λ { ≤-zero      ≤-zero      → refl
    ; (≤-suc m≤n) (≤-suc n≤m) → ap suc (antisym≤ ℕ-poset m≤n n≤m) }
