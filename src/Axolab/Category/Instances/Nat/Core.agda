
module Axolab.Category.Instances.Nat.Core where

open import Axolab.Prelude
open import Axolab.Prelude.Primitive.Nat public

infix 6 _≤_

-- ---------------------------------------------------------------------------------------------------------------------

data _≤_ : ℕ → ℕ → Setoid where
  ≤-zero : {n   : ℕ} → 0 ≤ n
  ≤-suc  : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-reflexive : {m n : ℕ} → m ≡ n → m ≤ n
≤-reflexive {zero}  refl = ≤-zero
≤-reflexive {suc _} refl = ≤-suc (≤-reflexive refl)

≤-refl : {m : ℕ} → m ≤ m
≤-refl = ≤-reflexive refl

≤-trans : {m n o : ℕ} → n ≤ o → m ≤ n → m ≤ o
≤-trans _           ≤-zero      = ≤-zero
≤-trans (≤-suc n≤o) (≤-suc m≤n) = ≤-suc (≤-trans n≤o m≤n)

≤-id← : ∀ {m n} (m≤n : m ≤ n) → ≤-trans ≤-refl m≤n ≡ m≤n
≤-id← ≤-zero      = refl
≤-id← (≤-suc m≤n) = ap ≤-suc (≤-id← m≤n)

≤-id⇢ : ∀ {m n} (m≤n : m ≤ n) → ≤-trans m≤n ≤-refl ≡ m≤n
≤-id⇢ ≤-zero      = refl
≤-id⇢ (≤-suc m≤n) = ap ≤-suc (≤-id⇢ m≤n)

≤-assoc← : ∀ {m n o p} (o≤p : o ≤ p) (n≤o : n ≤ o) (m≤n : m ≤ n) →
  ≤-trans o≤p (≤-trans n≤o m≤n) ≡ ≤-trans (≤-trans o≤p n≤o) m≤n
≤-assoc← o≤p         n≤o         ≤-zero      = refl
≤-assoc← (≤-suc o≤p) (≤-suc n≤o) (≤-suc m≤n) = ap ≤-suc (≤-assoc← o≤p n≤o m≤n)
