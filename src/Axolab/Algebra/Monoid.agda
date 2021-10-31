
module Axolab.Algebra.Monoid where

open import Axolab.Algebra.Theory
open import Axolab.Data.Fin
open import Axolab.Data.Product
open import Axolab.Data.Vect
open import Axolab.Prelude

open Signature
open Theory

-- ---------------------------------------------------------------------------------------------------------------------

data MonoidOps : Setoid where
  unit : MonoidOps
  ⨂    : MonoidOps

data MonoidLaws : Setoid where
  associativity  : MonoidLaws
  left-identity  : MonoidLaws
  right-identity : MonoidLaws

monoid : Theory 0ℓ 0ℓ
signature monoid .operations = MonoidOps
signature monoid .o-arities  =
  λ { unit → 0
    ; ⨂    → 2 }
laws      monoid = MonoidLaws
l-arities monoid =
  λ { associativity  → 3
    ; left-identity  → 1
    ; right-identity → 1 }
l-relates monoid =
  λ { associativity
      → op ⨂ (var zero ∷ op ⨂ (var (suc zero) ∷ var (suc (suc zero)) ∷ nil) ∷ nil)
      , op ⨂ (op ⨂ (var zero ∷ var (suc zero) ∷ nil) ∷ var (suc (suc zero)) ∷ nil)
    ; left-identity
      → var zero
      , op ⨂ (op unit nil ∷ var zero ∷ nil)
    ; right-identity
      → var zero
      , op ⨂ (var zero ∷ op unit nil ∷ nil)
    }

Monoid : (ℓ : Level) → Setoid (lsuc ℓ)
Monoid = Model monoid
