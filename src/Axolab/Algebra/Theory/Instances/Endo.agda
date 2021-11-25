
open import Axolab.Category

module Axolab.Algebra.Theory.Instances.Endo {o ℓ} (C : Category o ℓ) where

open import Axolab.Algebra.Theory
open import Axolab.Algebra.Theory.Structure.Monoid
open import Axolab.Prelude

open Category C
open Interpretation
open Model

-- ---------------------------------------------------------------------------------------------------------------------

endo : Ob → Setoid ℓ
endo A = Hom A A

endo⊨monoid : {A : Ob} → endo A ⊨ monoid
interp endo⊨monoid =
  λ { unit → id
    ; ⨂    → λ f g → f ∘ g }
sound  endo⊨monoid =
  λ { associativity  _ → sym assoc→
    ; left-identity  _ → sym id←
    ; right-identity _ → sym id→ }

Endo : (A : Ob) → Monoid ℓ
model  (Endo A) = endo A
models (Endo A) = endo⊨monoid
