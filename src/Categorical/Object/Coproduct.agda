open import Categorical.Category

module Categorical.Object.Coproduct {o ℓ} (C : Category o ℓ) where

open import Prelude
open import Prelude.Equality

open Category C

private
  variable
    A B X Y Z : Ob
    f g h : Hom A B

-- ---------------------------------------------------------------------------------------------------------------------

infixr 6 Coproduct

syntax Coproduct A B = A ∐ B

record Coproduct (A B : Ob) : Setoid (o ⊔ ℓ) where
  infix 10 [_,_]

  field
    A+B   : Ob
    inj₁  : Hom A A+B
    inj₂  : Hom B A+B
    [_,_] : Hom A X → Hom B X → Hom A+B X

  field
    inject₁ : [ f , g ] ∘ inj₁ ≡ f
    inject₂ : [ f , g ] ∘ inj₂ ≡ g
    unique  : h ∘ inj₁ ≡ f → h ∘ inj₂ ≡ g → [ f , g ] ≡ h
