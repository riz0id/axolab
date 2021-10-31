
module Axolab.Data.Vect where

open import Axolab.Data.Fin
open import Axolab.Data.Nat.Core
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

infixr 40 _∷_
infix  10 _‼_

data Vect {ℓ} (A : Setoid ℓ) : ℕ → Setoid ℓ where
  nil : Vect A 0
  _∷_ : {n : ℕ} → A → Vect A n → Vect A (1 + n)

_‼_ : ∀ {ℓ} {A : Setoid ℓ} {n : ℕ} → Vect A n → Fin n → A
x ∷ xs ‼ zero  = x
x ∷ xs ‼ suc i = xs ‼ i

map : ∀ {ℓ ℓ'}  {A : Setoid ℓ} {B : Setoid ℓ'} {n : ℕ} → (A → B) → Vect A n → Vect B n
map f nil      = nil
map f (x ∷ xs) = f x ∷ map f xs
