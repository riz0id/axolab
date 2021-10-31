
open import Categorical.Category

module Categorical.Object.Exponential {o ℓ} (C : Category o ℓ) where

open import Categorical.Object.Product C
open import Prelude
open import Prelude.Equality

open Category C

private
  variable
    A B X Y : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Exponential (A B : Ob) : Setoid (o ⊔ ℓ) where
  field
    B^A     : Ob
    product : Product B^A A

  module product = Product product

  B^A×A : Ob
  B^A×A = product.A×B

  field
    eval : Hom B^A×A B
    λf   : (X×A : Product X A) (f : Hom (Product.A×B X×A) B) → Hom X B^A

  field
    β : (X×A : Product X A) → {g : Hom (Product.A×B X×A) B} →
        eval ∘ {![ ? ⇒ ? ]!} ≡ g
