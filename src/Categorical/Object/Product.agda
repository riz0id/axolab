open import Categorical.Category

module Categorical.Object.Product {o ℓ} (C : Category o ℓ) where

open import Categorical.Category.Instances.Product
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

open Category C

record Product (A B : Ob) : Setoid (o ⊔ ℓ) where
  infix 10 ⟨_,_⟩

  field
    A×B   : Ob
    pi₁   : Hom A×B A
    pi₂   : Hom A×B B
    ⟨_,_⟩ : {C : Ob} → Hom C A → Hom C B → Hom C A×B

  field
    project₁ : {C : Ob} {f : Hom C A} {g : Hom C B} → pi₁ ∘ ⟨ f , g ⟩ ≡ f
    project₂ : {C : Ob} {f : Hom C A} {g : Hom C B} → pi₂ ∘ ⟨ f , g ⟩ ≡ g
    unique   : {C : Ob} {f : Hom C A} {g : Hom C B} {h : Hom C A×B} →
      pi₁ ∘ h ≡ f → pi₂ ∘ h ≡ g → ⟨ f , g ⟩ ≡ h
