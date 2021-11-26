
module Axolab.Prelude.Primitive.Vect where

open import Axolab.Prelude.Primitive.Fin
open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

infixr 40 _∷_
infix  10 _‼_

data Vect {ℓ} (A : Setoid ℓ) : ℕ → Setoid ℓ where
  nil : Vect A 0
  _∷_ : {n : ℕ} → A → Vect A n → Vect A (1 + n)

_‼_ : ∀ {ℓ} {A : Setoid ℓ} {n : ℕ} → Vect A n → Fin n → A
x ∷ xs ‼ fzero  = x
x ∷ xs ‼ fsuc i = xs ‼ i

map : ∀ {ℓ ℓ'}  {A : Setoid ℓ} {B : Setoid ℓ'} {n : ℕ} → (A → B) → Vect A n → Vect B n
map f nil      = nil
map f (x ∷ xs) = f x ∷ map f xs

tabulate : ∀ {ℓ n} {A : Setoid ℓ} → (Fin n → A) → Vect A n
tabulate {n = zero}  f = nil
tabulate {n = suc n} f = f fzero ∷ tabulate (λ n → f (fsuc n))
