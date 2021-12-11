
module Axolab.Algebra.Operad where

open import Axolab.Data.Fin
open import Axolab.Data.Nat
open import Axolab.Data.Product
open import Axolab.Data.Vec
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------


data Op (ℓ : Level) : Signature ℓ where
  unit : Op ℓ 0
  ⨂    : Op ℓ 2

data Law (ℓ : Level) : Signature ℓ where
  assoc     : Law ℓ 3
  identity← : Law ℓ 1
  identity→ : Law ℓ 1


open Theory

monoid : (o ℓ : Level) → Theory o ℓ
signature   (monoid o ℓ) = Op o
laws        (monoid o ℓ) = Law ℓ
laws-interp (monoid o ℓ) =
  λ { assoc
      → term ⨂ (term ⨂ (var (# 0) ∷ var (# 1) ∷ nil) ∷ var (# 2) ∷ nil)
      , term ⨂ (var (# 0) ∷ term ⨂ (var (# 0) ∷ var (# 2) ∷ nil) ∷ nil)
    ; identity←
      → term ⨂ (term unit nil ∷ var fzero ∷ nil)
      , var (# 0)
    ; identity→
      → term ⨂ (var (# 0) ∷ term unit nil ∷ nil)
      , var (# 0) }

-- laws : Law 3 → Term Op 3
-- laws assoc = term ⨂ (term ⨂ (var (# 0) ∷ var (# 1) ∷ nil) ∷ var (# 2) ∷ nil)
