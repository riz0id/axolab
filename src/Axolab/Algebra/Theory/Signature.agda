
module Axolab.Algebra.Theory.Signature where

open import Axolab.Prelude.Primitive.Nary
open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude.Primitive.Vect
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record Signature (ℓ : Level) : Set (lsuc ℓ) where
  field
    ops     : Set ℓ
    arities : ops → ℕ

open Signature public

Interprets : ∀ {ℓ ℓ'} (A : Set ℓ) (S : Signature ℓ') → Set (ℓ ⊔ ℓ')
Interprets A S = (o : ops S) → λ⟨ arities S o ⟩ A ⇒ A
