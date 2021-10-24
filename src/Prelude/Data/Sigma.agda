{-# OPTIONS --safe #-}

module Prelude.Data.Sigma where

open import Prelude.Primitive

-- ---------------------------------------------------------------------------------------------------------------------

infix  2 Σ
infixr 5 _,_

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

record Σ {ℓ ℓ'} (A : Setoid ℓ) (B : A → Setoid ℓ') : Setoid (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst
