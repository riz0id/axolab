open import Axolab.Category

module Axolab.Category.Structure.Cartesian {o ℓ} (C : Category o ℓ) where

open import Axolab.Category.Functor
open import Axolab.Category.Functor.Bifunctor
open import Axolab.Category.Object.Terminal
open import Axolab.Data.Product using (_,_; fst; snd)
open import Axolab.Prelude

open Category C
open Functor

private
  variable
    X Y Z W : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Cartesian : Setoid (o ⊔ ℓ) where
  infixr 5 _×₀_ _×₁_

  field
    _×₀_ : Ob → Ob → Ob
    _×₁_ : Hom X Y → Hom X Z → Hom X (Y ×₀ Z)

  field
    π₁ : Hom (X ×₀ Y) X
    π₂ : Hom (X ×₀ Y) Y

  field
    π₁×₁≡id    : {f : Hom X Y} {g : Hom X Z} → π₁ ∘ (f ×₁ g) ≡ f
    π₂×₁≡id    : {f : Hom X Y} {g : Hom X Z} → π₂ ∘ (f ×₁ g) ≡ g
    ×-unique   : {f : Hom X Y} {g : Hom X Z} {h : Hom X (Y ×₀ Z)} → f ≡ π₁ ∘ h → g ≡ π₂ ∘ h → h ≡ (f ×₁ g)
    ⊤-terminal : Terminal C

  open Terminal ⊤-terminal public
  open PropReasoning

  ×-unique₂ : {f g : Hom (X ×₀ Y) (Y ×₀ Z)} → π₁ ∘ f ≡ π₁ ∘ g → π₂ ∘ f ≡ π₂ ∘ g → f ≡ g
  ×-unique₂ {f = f} {g = g} p q = ×-unique (sym p) (sym q) ∘p sym (×-unique refl refl)

  π₁×π₂≡id : π₁ ×₁ π₂ ≡ id {X ×₀ Y}
  π₁×π₂≡id = sym (×-unique (sym id→) (sym id→))

  ×₁-distrib : (f : Hom X Y) (g : Hom X Z) (h : Hom W X) → (f ×₁ g) ∘ h ≡ f ∘ h ×₁ g ∘ h
  ×₁-distrib f g h = ×-unique (ap (_∘ h) (sym π₁×₁≡id) ∘p assoc→) (ap (_∘ h) (sym π₂×₁≡id) ∘p assoc→)

  -×- : Bifunctor C C C
  F₀   -×- (A , B) = A ×₀ B
  F₁   -×- (f , g) = f ∘ π₁ ×₁ g ∘ π₂
  F-id -×- =
    id ∘ π₁ ×₁ id ∘ π₂ ≡⟨ ap₂ _×₁_ id← id← ⟩
    π₁ ×₁ π₂           ≡⟨ π₁×π₂≡id ⟩
    id                 ∎
  F-∘ -×- (f , g) (h , i) =
    (f ∘ h) ∘ π₁ ×₁ (g ∘ i) ∘ π₂ ≡⟨ ap₂ _×₁_ assoc→ assoc→ ⟩
    f ∘ h ∘ π₁ ×₁ g ∘ i ∘ π₂ ≡⟨ ×-unique (sym (π₁×₁≡id ∘p π₁-∘)) (sym (π₂×₁≡id ∘p π₂-∘)) ⟩
    (f ∘ π₁) ∘ (h ∘ π₁ ×₁ i ∘ π₂) ×₁ (g ∘ π₂) ∘ (h ∘ π₁ ×₁ i ∘ π₂) ≡⟨ sym (×₁-distrib _ _ _) ⟩
    (f ∘ π₁ ×₁ g ∘ π₂) ∘ (h ∘ π₁ ×₁ i ∘ π₂) ∎
    where
      π₁-∘ : f ∘ h ∘ π₁ ≡ (f ∘ π₁) ∘ (h ∘ π₁ ×₁ i ∘ π₂)
      π₁-∘ =
        f ∘ h ∘ π₁ ≡⟨ ap (f ∘_) (sym π₁×₁≡id) ⟩
        f ∘ π₁ ∘ (h ∘ π₁ ×₁ i ∘ π₂) ≡⟨ assoc← ⟩
        (f ∘ π₁) ∘ (h ∘ π₁ ×₁ i ∘ π₂) ∎

      π₂-∘ : g ∘ i ∘ π₂ ≡ (g ∘ π₂) ∘ (h ∘ π₁ ×₁ i ∘ π₂)
      π₂-∘ =
        g ∘ i ∘ π₂ ≡⟨ ap (g ∘_) (sym π₂×₁≡id) ⟩
        g ∘ π₂ ∘ (h ∘ π₁ ×₁ i ∘ π₂) ≡⟨ assoc← ⟩
        (g ∘ π₂) ∘ (h ∘ π₁ ×₁ i ∘ π₂) ∎

  _×- : (A : Ob) → Endofunctor C
  A ×- = Left -×- A

  -×_ : (A : Ob) → Endofunctor C
  -× A = Right -×- A
