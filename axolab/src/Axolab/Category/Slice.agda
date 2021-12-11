
open import Axolab.Category

module Axolab.Category.Slice {o ℓ} (C : Category o ℓ) where

open import Axolab.Data.Product
open import Axolab.Prelude

open Category
open PropReasoning

private
  module C = Category C

-- ---------------------------------------------------------------------------------------------------------------------

Slice : C.Ob → Category (o ⊔ ℓ) ℓ
Ob     (Slice S) = Σ[ A ∈ C.Ob ] C.Hom A S
Hom    (Slice S) = λ where (A , f) (B , g) → Σ[ h ∈ C.Hom A B ] g C.∘ h ≡ f
id     (Slice S) = C.id , C.id→
_∘_    (Slice S) {X} {Y} {Z} = λ where
  (f , fib₁) (g , fib₂) →
    let p = snd Z C.∘ f C.∘ g   ≡⟨ C.assoc← ⟩
            (snd Z C.∘ f) C.∘ g ≡⟨ ap (C._∘ g) fib₁ ⟩
            snd Y C.∘ g         ≡⟨ fib₂ ⟩
            snd X ∎
     in f C.∘ g , p
id←    (Slice S) = Σ-Path C.id← (UIP _ _)
id→    (Slice S) = Σ-Path C.id→ (UIP _ _)
assoc← (Slice S) = Σ-Path C.assoc← (UIP _ _)
assoc→ (Slice S) = Σ-Path C.assoc→ (UIP _ _)

Coslice : C.Ob → Category (o ⊔ ℓ) ℓ
Ob     (Coslice S) = Σ[ A ∈ C.Ob ] C.Hom S A
Hom    (Coslice S) = λ where (A , f) (B , g) → Σ[ h ∈ C.Hom A B ] g ≡ h C.∘ f
id     (Coslice S) = C.id , sym C.id←
_∘_    (Coslice S) {X} {Y} {Z} = λ where
  (f , fib₁) (g , fib₂) →
    let p = snd Z               ≡⟨ fib₁ ⟩
            f C.∘ snd Y         ≡⟨ ap (f C.∘_) fib₂ ⟩
            f C.∘ g C.∘ snd X   ≡⟨ C.assoc← ⟩
            (f C.∘ g) C.∘ snd X ∎
     in f C.∘ g , p
id←    (Coslice S) = Σ-Path C.id← (UIP _ _)
id→    (Coslice S) = Σ-Path C.id→ (UIP _ _)
assoc← (Coslice S) = Σ-Path C.assoc← (UIP _ _)
assoc→ (Coslice S) = Σ-Path C.assoc→ (UIP _ _)
