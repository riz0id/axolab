
module Axolab.Algebra.Theory.Structure.Group where

open import Axolab.Algebra.Theory
open import Axolab.Data.Product
open import Axolab.Prelude.Primitive.Fin
open import Axolab.Prelude.Primitive.Vect
open import Axolab.Prelude

open Signature
open Theory

-- ---------------------------------------------------------------------------------------------------------------------

data GroupOp : Set where
  unit : GroupOp
  inv  : GroupOp
  ⨂    : GroupOp

data GroupLaw : Set where
  associativity  : GroupLaw
  left-identity  : GroupLaw
  right-identity : GroupLaw
  left-inverse   : GroupLaw
  right-inverse  : GroupLaw

group : Theory 0ℓ 0ℓ
signature group .operations = GroupOp
signature group .o-arities  =
  λ { unit → 0
    ; inv  → 1
    ; ⨂    → 2 }
laws      group = GroupLaw
l-arities group =
  λ { associativity  → 3
    ; left-identity  → 1
    ; right-identity → 1
    ; left-inverse   → 1
    ; right-inverse  → 1 }
l-relates group =
  λ { associativity
      → op ⨂ (var fzero ∷ op ⨂ (var (fsuc fzero) ∷ var (fsuc (fsuc fzero)) ∷ nil) ∷ nil)
      , op ⨂ (op ⨂ (var fzero ∷ var (fsuc fzero) ∷ nil) ∷ var (fsuc (fsuc fzero)) ∷ nil)
    ; left-identity
      → var fzero
      , op ⨂ (op unit nil ∷ var fzero ∷ nil)
    ; right-identity
      → var fzero
      , op ⨂ (var fzero ∷ op unit nil ∷ nil)
    ; left-inverse
      → op ⨂ (op inv (var fzero ∷ nil) ∷ var fzero ∷ nil)
      , op unit nil
    ; right-inverse
      → op ⨂ (var fzero ∷ op inv (var fzero ∷ nil) ∷ nil)
      , op unit nil }

Group : (ℓ : Level) → Set (lsuc ℓ)
Group = Model group
