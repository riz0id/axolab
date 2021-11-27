
module Axolab.Data.Nat where

open import Axolab.Data.Nat.Core public
open import Axolab.Prelude

infix 6 _≤_ _<_

-- ---------------------------------------------------------------------------------------------------------------------

data _≤_ : ℕ → ℕ → Set where
  ≤-zero : {n   : ℕ} → 0 ≤ n
  ≤-suc  : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (≤-suc m≤n) = m≤n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

-- ℕ[+]⊨monoid : ℕ ⊨ monoid
-- ℕ[+]⊨monoid = mon where
--   open Interpretation
--   open Signature
--   open Theory

--   +id→ : (n : ℕ) → n ≡ n + 0
--   +id→ zero    = refl
--   +id→ (suc n) = ap suc (+id→ n)

--   +assoc← : (m n o : ℕ) → m + (n + o) ≡ m + n + o
--   +assoc← zero    n o = refl
--   +assoc← (suc m) n o = ap suc (+assoc← m n o)

--   mon : ℕ ⊨ monoid
--   interp mon unit nil           = 0
--   interp mon ⨂    (m ∷ n ∷ nil) = m + n
--   sound  mon associativity  (m ∷ n ∷ o ∷ nil) = +assoc← m n o
--   sound  mon left-identity  (n ∷ nil) = refl
--   sound  mon right-identity (n ∷ nil) = +id→ n
