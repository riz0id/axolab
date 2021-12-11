
module Axolab.Data.Nat.Core where

open import Axolab.Prelude
open import Axolab.Relation.Negation

open import Agda.Builtin.Nat public
  using    ( suc; zero
           ; _+_; _*_ )
  renaming ( Nat to ℕ
           ; _-_ to _∸_
           ; _==_ to _≡b_; _<_ to _<b_ )

infix 5 _≤_ _<_ _≮_ _>_ _≯_

-- ---------------------------------------------------------------------------------------------------------------------

data _≤_ : ℕ → ℕ → Set where
  ≤-zero : {n   : ℕ} → 0 ≤ n
  ≤-suc  : {m n : ℕ} → m ≤ n → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

_≥_ : ℕ → ℕ → Set
m ≥ n = n ≤ m

_>_ : ℕ → ℕ → Set
m > n = n < m

_≰_ : ℕ → ℕ → Set
a ≰ b = ¬ a ≤ b

_≮_ : ℕ → ℕ → Set
a ≮ b = ¬ a < b

_≱_ : ℕ → ℕ → Set
a ≱ b = ¬ a ≥ b

_≯_ : ℕ → ℕ → Set
a ≯ b = ¬ a > b
