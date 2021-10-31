open import Categorical.Category

module Categorical.Object.Product {o ℓ} (C : Category o ℓ) where

open import Prelude
open import Prelude.Equality

open Category C

private
  variable
    A B X Y Z : Ob
    f : Hom X A
    g : Hom X B

-- ---------------------------------------------------------------------------------------------------------------------

infix 6 Product

syntax Product A B = A ∏ B

record Product (A B : Ob) : Setoid (o ⊔ ℓ) where
  infix 10 ⟨_,_⟩

  field
    A×B   : Ob
    pi₁   : Hom A×B A
    pi₂   : Hom A×B B
    ⟨_,_⟩ : Hom X A → Hom X B → Hom X A×B

  field
    project₁ : pi₁ ∘ ⟨ f , g ⟩ ≡ f
    project₂ : pi₂ ∘ ⟨ f , g ⟩ ≡ g
    unique   : {h : Hom X A×B} → pi₁ ∘ h ≡ f → pi₂ ∘ h ≡ g → ⟨ f , g ⟩ ≡ h
