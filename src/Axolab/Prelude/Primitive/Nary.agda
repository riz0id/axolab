
module Axolab.Prelude.Primitive.Nary where

open import Axolab.Prelude.Primitive
open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude.Primitive.Vect

-- ---------------------------------------------------------------------------------------------------------------------

-- 0ℓ-level n-arity lambdas.
--
λ⟨_⟩_⇒_ : {ℓ : Level} → ℕ → Setoid ℓ → Setoid ℓ → Setoid ℓ
λ⟨ zero  ⟩ A ⇒ B = B
λ⟨ suc n ⟩ A ⇒ B = A → λ⟨ n ⟩ A ⇒ B

-- Vector application of n-arity lambdas.
--
_$⟨_⟩ : ∀ {ℓ n} {A B : Setoid ℓ} → λ⟨ n ⟩ A ⇒ B → Vect A n → B
f $⟨ nil    ⟩ = f
f $⟨ x ∷ xs ⟩ = f x $⟨ xs ⟩
