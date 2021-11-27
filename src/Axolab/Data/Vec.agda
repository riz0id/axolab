
module Axolab.Data.Vec where

open import Axolab.Data.Fin
open import Axolab.Data.Nat
open import Axolab.Prelude

open import Axolab.Data.Vec.Core public

infix  10 _‼_

-- ---------------------------------------------------------------------------------------------------------------------

_‼_ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Vec A n → Fin n → A
x ∷ xs ‼ fzero  = x
x ∷ xs ‼ fsuc i = xs ‼ i

map : ∀ {ℓ ℓ'}  {A : Set ℓ} {B : Set ℓ'} {n : ℕ} → (A → B) → Vec A n → Vec B n
map f nil      = nil
map f (x ∷ xs) = f x ∷ map f xs

tabulate : ∀ {ℓ n} {A : Set ℓ} → (Fin n → A) → Vec A n
tabulate {n = zero}  f = nil
tabulate {n = suc n} f = f fzero ∷ tabulate (λ n → f (fsuc n))
