
module Axolab.Data.Nat where

open import Axolab.Data.Bool
open import Axolab.Data.Top
open import Axolab.Relation.Decidable as Dec
open import Axolab.Relation.Negation
open import Axolab.Relation.Trichotomy
open import Axolab.Prelude hiding (_⊔_)
open import Axolab.Prelude.Function

open import Axolab.Data.Nat.Core public
open import Axolab.Data.Nat.Properties

infixl 6 _⊔_
infixl 7 _⊓_

-- ---------------------------------------------------------------------------------------------------------------------

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (≤-suc m≤n) = m≤n

_≡?_ : (m n : ℕ) → Dec (m ≡ n)
m ≡? n = Dec.map (≡b→≡ m n) (≡→≡b m n) (T? (m ≡b n))

_<?_ : (m n : ℕ) → Dec (m < n)
m <? n = Dec.map (<b→< m n) (<→<b m n) (T? (m <b n))

compare : (m n : ℕ) → Trichotomy (m < n) (m ≡ n) (m > n)
compare m n with m ≡? n | m <? n
... | because _ (of-yes m≡n) | because _ (of-yes m<n) = contradiction m≡n (send<→≢ m<n)
... | because _ (of-yes m≡n) | because _ (of-no  m≮n) = tri≈ m≮n m≡n (irrefl< (sym m≡n))
... | because _ (of-no  m≢n) | because _ (of-yes m<n) = tri< m<n m≢n (send<→≯ m<n)
... | because _ (of-no  m≢n) | because _ (of-no  m≮n) = tri> m≮n m≢n (send≤×≢→< (send≮→≥ m≮n) (m≢n ∘ sym))

-- Max/Ceiling
_⊔_ : ℕ → ℕ → ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

-- Min/Floor
_⊓_ : ℕ → ℕ → ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

