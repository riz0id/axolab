
module Axolab.Data.Nat.Properties where

open import Axolab.Data.Bool
open import Axolab.Data.Bot
open import Axolab.Data.Coproduct
open import Axolab.Data.Top
open import Axolab.Relation.Negation
open import Axolab.Prelude

open import Axolab.Data.Nat.Core as Nat

private
  variable
    m n o p : ℕ

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _≡_

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

≡→≡b : (m n : ℕ) → m ≡ n → T (m ≡b n)
≡→≡b zero    zero    refl = tt
≡→≡b (suc m) (suc m) refl = ≡→≡b m m refl

≡b→≡ : (m n : ℕ) → T (m ≡b n) → m ≡ n
≡b→≡ zero    zero    p = refl
≡b→≡ (suc m) (suc n) p = ap suc (≡b→≡ m n p)

ℕ-isSet : (p q : m ≡ n) → p ≡ q
ℕ-isSet refl refl = refl

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _≤_

n≤1+n : n ≤ 1 + n
n≤1+n {zero}  = ≤-zero
n≤1+n {suc n} = ≤-suc n≤1+n

send≤→≯ : {m n : ℕ} → m ≤ n → m ≯ n
send≤→≯ (≤-suc m≤n) (≤-suc m≯n) = send≤→≯ m≤n m≯n

send≤×≢→< : {m n : ℕ} → m ≤ n → m ≢ n → m < n
send≤×≢→< {n = zero}  ≤-zero m≢n = contradiction refl m≢n
send≤×≢→< {n = suc n} ≤-zero m≢n = ≤-suc ≤-zero
send≤×≢→< (≤-suc m≤n) m≢n = ≤-suc (send≤×≢→< m≤n λ e → m≢n (ap suc e))

reflexive≤ : m ≡ n → m ≤ n
reflexive≤ {zero}  refl = ≤-zero
reflexive≤ {suc m} refl = ≤-suc (reflexive≤ refl)

refl≤ : m ≤ m
refl≤ = reflexive≤ refl

trans≤ : m ≤ n → n ≤ o → m ≤ o
trans≤ ≤-zero    q         = ≤-zero
trans≤ (≤-suc p) (≤-suc q) = ≤-suc (trans≤ p q)

isProp≤ : (p q : m ≤ n) → p ≡ q
isProp≤ ≤-zero    ≤-zero    = refl
isProp≤ (≤-suc p) (≤-suc q) = ap ≤-suc (isProp≤ p q)

antisym≤ : m ≤ n → n ≤ m → m ≡ n
antisym≤ ≤-zero    ≤-zero    = refl
antisym≤ (≤-suc p) (≤-suc q) = ap suc (antisym≤ p q)

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _<_

reflects</suc : suc m < suc n → m < n
reflects</suc (≤-suc m<n) = m<n

send<→≤ : {m n : ℕ} → m < n → m ≤ n
send<→≤ (≤-suc ≤-zero)      = ≤-zero
send<→≤ (≤-suc (≤-suc m<n)) = ≤-suc (send<→≤ (≤-suc m<n))

send<→≢ : m < n → m ≢ n
send<→≢ (≤-suc m<n) refl = send<→≢ m<n refl

send<→≯ : m < n → m ≯ n
send<→≯ (≤-suc m<n) (≤-suc m≯n) = send<→≯ m<n m≯n

<→<b : (m n : ℕ) → m < n → T (m <b n)
<→<b zero    (suc n) p = tt
<→<b (suc m) (suc n) p = <→<b m n (reflects</suc p)

<b→< : (m n : ℕ) → T (m <b n) → m < n
<b→< zero    (suc n) p = ≤-suc ≤-zero
<b→< (suc m) (suc n) p = ≤-suc (<b→< m n p)

irrefl< : m ≡ n → m < n → ⊥
irrefl< refl (≤-suc m<n) = irrefl< refl m<n

trans< : m < n → n < o → m < o
trans< (≤-suc p) (≤-suc q) = ≤-suc (trans≤ p (trans≤ n≤1+n q))

isProp< : (p q : m < n) → p ≡ q
isProp< (≤-suc ≤-zero)    (≤-suc ≤-zero)    = refl
isProp< (≤-suc (≤-suc p)) (≤-suc (≤-suc q)) = ap ≤-suc (isProp< (≤-suc p) (≤-suc q))

antisym< : m < n → n < m → m ≡ n
antisym< (≤-suc p) (≤-suc q) = ap suc (antisym< p q)

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _≰_

send¬≤→¬< : {m n : ℕ} → m ≰ n → m ≮ n
send¬≤→¬< m≰n m≮n = m≰n (send<→≤ m≮n)

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _>_

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _≮_

send≮→≥ : m ≮ n → m ≥ n
send≮→≥ {_}     {zero}  m≮n = ≤-zero
send≮→≥ {zero}  {suc n} m≮n = contradiction (≤-suc ≤-zero) m≮n
send≮→≥ {suc m} {suc n} m≮n = ≤-suc (send≮→≥ (λ z → m≮n (≤-suc z)))

-- ---------------------------------------------------------------------------------------------------------------------
--

trans</≤→< : m < n → n ≤ o → m < o
trans</≤→< (≤-suc m<n) (≤-suc n≤o) = ≤-suc (trans≤ m<n n≤o)
