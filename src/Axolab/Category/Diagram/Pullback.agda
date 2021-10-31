
open import Axolab.Category

module Axolab.Category.Diagram.Pullback {o ℓ} (C : Category o ℓ) where

open import Axolab.Prelude

open Category C

private
  variable
    P Q X Y Z : Ob
    q₁ q₂ : Hom Q X

-- ---------------------------------------------------------------------------------------------------------------------

record Pullback (p₁ : Hom P X) (p₂ : Hom P Y) (f : Hom X Z) (g : Hom Y Z) : Setoid (o ⊔ ℓ) where
  field
    commutes : f ∘ p₁ ≡ g ∘ p₂
    limiting : f ∘ q₁ ≡ g ∘ q₂ → Hom Q P
    unique   : {i : Hom Q P} (eq : f ∘ q₁ ≡ g ∘ q₂) → p₁ ∘ i ≡ q₁ → p₂ ∘ i ≡ q₂ → i ≡ limiting eq

  field
    p₁∘limiting≡q₁ : (eq : f ∘ q₁ ≡ g ∘ q₂) → p₁ ∘ limiting eq ≡ q₁
    p₂∘limiting≡q₂ : (eq : f ∘ q₁ ≡ g ∘ q₂) → p₂ ∘ limiting eq ≡ q₂
