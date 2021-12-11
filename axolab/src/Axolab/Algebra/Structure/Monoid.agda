
module Axolab.Algebra.Theory.Structure.Monoid where

open import Axolab.Algebra.Theory
open import Axolab.Category
open import Axolab.Category.Instances.Models
open import Axolab.Data.Product
open import Axolab.Prelude.Primitive.Fin
open import Axolab.Prelude.Primitive.Vect
open import Axolab.Prelude

open Signature
open Theory

-- ---------------------------------------------------------------------------------------------------------------------

data MonoidOp : Set where
  unit : MonoidOp
  ⨂    : MonoidOp

data MonoidLaw : Set where
  associativity  : MonoidLaw
  left-identity  : MonoidLaw
  right-identity : MonoidLaw

monoid : Theory 0ℓ 0ℓ
signature monoid .operations = MonoidOp
signature monoid .o-arities  =
  λ { unit → 0
    ; ⨂    → 2 }
laws      monoid = MonoidLaw
l-arities monoid =
  λ { associativity  → 3
    ; left-identity  → 1
    ; right-identity → 1 }
l-relates monoid =
  λ { associativity
      → op ⨂ (var fzero ∷ op ⨂ (var (fsuc fzero) ∷ var (fsuc (fsuc fzero)) ∷ nil) ∷ nil)
      , op ⨂ (op ⨂ (var fzero ∷ var (fsuc fzero) ∷ nil) ∷ var (fsuc (fsuc fzero)) ∷ nil)
    ; left-identity
      → var fzero
      , op ⨂ (op unit nil ∷ var fzero ∷ nil)
    ; right-identity
      → var fzero
      , op ⨂ (var fzero ∷ op unit nil ∷ nil) }

Monoid : (ℓ : Level) → Set (lsuc ℓ)
Monoid = Model monoid

Mon : (ℓ : Level) → Category (lsuc ℓ) ℓ
Mon _ = monoid -Models
