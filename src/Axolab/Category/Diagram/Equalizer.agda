
open import Axolab.Category

module Axolab.Category.Diagram.Equalizer {o ℓ} (C : Category o ℓ) where

open import Axolab.Prelude

open Category C

private
  variable
    E E' A B : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Equalizer (f g : Hom A B) (e : Hom E A) : Setoid (o ⊔ ℓ) where
  field
    commutes : f ∘ e ≡ g ∘ e
    limiting : {e' : Hom E' A} → f ∘ e' ≡ g ∘ e' → Hom E' E
    unique   : {e' : Hom E' A} {i : Hom E' E} → (eq : f ∘ e' ≡ g ∘ e') → e' ≡ e ∘ i → i ≡ limiting eq

  field
    e∘limiting≡e' : {e' : Hom E' A} → (eq : f ∘ e' ≡ g ∘ e') → e ∘ limiting eq ≡ e'

  monic : {h i : Hom E' E} → e ∘ h ≡ e ∘ i → h ≡ i
  monic {h = h} {i = i} eq =
    h            ≡⟨ unique lim (sym eq) ⟩
    limiting lim ≡⟨ sym (unique lim refl) ⟩
    i            ∎
    where
      open PropReasoning

      lim : f ∘ e ∘ i ≡ g ∘ e ∘ i
      lim =
        f ∘ e ∘ i   ≡⟨ assoc← ⟩
        (f ∘ e) ∘ i ≡⟨ ap (_∘ i) commutes ⟩
        (g ∘ e) ∘ i ≡⟨ assoc→ ⟩
        g ∘ e ∘ i   ∎
