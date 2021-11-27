
module Axolab.Algebra.Theory.Term where

open import Axolab.Algebra.Theory.Signature
open import Axolab.Prelude.Primitive.Fin
open import Axolab.Prelude.Primitive.Nary
open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude.Primitive.Vect as Vect
open import Axolab.Prelude

open Signature

-- ---------------------------------------------------------------------------------------------------------------------

data Term {ℓ ℓ'}  (S : Signature ℓ) (n : Set ℓ') : Set (ℓ ⊔ ℓ') where
  var : n → Term S n
  op  : (o : ops S) → Vect (Term S n) (arities S o) → Term S n

mutual
  evaluate : ∀ {ℓ ℓ'} {n : ℕ} {A : Set ℓ} {S : Signature ℓ'}
    → Interprets A S → Vect A n → Term S (Fin n) → A
  evaluate ops vars (var idx) = vars ‼ idx
  evaluate ops vars (op o xs) = ops o $⟨ evaluate' ops vars xs ⟩

  evaluate' : ∀ {ℓ ℓ'} {n k : ℕ} {A : Set ℓ} {S : Signature ℓ'}
    → Interprets A S → Vect A k → Vect (Term S (Fin k)) n → Vect A n
  evaluate' f vars nil      = nil
  evaluate' f vars (x ∷ xs) = evaluate f vars x ∷ evaluate' f vars xs
