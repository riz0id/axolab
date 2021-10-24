module Categorical.Category where

open import Categorical.Category.Core public
open import Prelude
open import Prelude.Equality

private
  variable
    o ℓ : Level

-- ---------------------------------------------------------------------------------------------------------------------

module Commutation (C : Category o ℓ) where
  infix  1 [_⇒_]⟨_≡_⟩
  infixl 2 connect

  open Category C

  [_⇒_]⟨_≡_⟩ : (A B : Ob) → Hom A B → Hom A B → Setoid ℓ
  [ A ⇒ B ]⟨ f ≡ g ⟩ = f ≡ g

  connect : ∀ {A C : Ob} (B : Ob) → Hom A B → Hom B C → Hom A C
  connect B f g = g ∘ f

  syntax connect B f g = f ⇒⟨ B ⟩ g
