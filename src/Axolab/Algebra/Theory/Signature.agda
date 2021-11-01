
module Axolab.Algebra.Theory.Signature where

open import Axolab.Prelude.Primitive.Nary
open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude.Primitive.Vect
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record Signature (ℓ : Level) : Setoid (lsuc ℓ) where
  field
    operations : Setoid ℓ
    o-arities  : operations → Nat

open Signature

Interprets : ∀ {ℓ ℓ'} (A : Setoid ℓ) (S : Signature ℓ') → Setoid (ℓ ⊔ ℓ')
Interprets A S = (o : operations S) → λ⟨ o-arities S o ⟩ A ⇒ A
