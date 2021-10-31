
module Axolab.Algebra.Theory.Term where

open import Axolab.Algebra.Theory.Signature
open import Axolab.Data.Fin
open import Axolab.Data.Nat.Core
open import Axolab.Data.Vect
open import Axolab.Prelude

open Signature

-- ---------------------------------------------------------------------------------------------------------------------

data Term {ℓ ℓ'}  (S : Signature ℓ) (n : Setoid ℓ') : Setoid (ℓ ⊔ ℓ') where
  var : n → Term S n
  op  : (o : operations S) → Vect (Term S n) (o-arities S o) → Term S n

mutual
  evaluate : ∀ {ℓ ℓ'} {n : ℕ} {A : Setoid ℓ} {S : Signature ℓ'}
    → Interprets A S → Vect A n → Term S (Fin n) → A
  evaluate ops vars (var ix) = vars ‼ ix
  evaluate ops vars (op o x) = ops o (evaluate' ops vars x)

  evaluate' : ∀ {ℓ ℓ'} {n k : ℕ} {A : Setoid ℓ} {S : Signature ℓ'}
    → Interprets A S → Vect A k → Vect (Term S (Fin k)) n → Vect A n
  evaluate' f vars nil      = nil
  evaluate' f vars (x ∷ xs) = evaluate f vars x ∷ evaluate' f vars xs
