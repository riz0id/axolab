
module Axolab.Category.Functor.Hom where

open import Axolab.Category
open import Axolab.Category.Instances.Product
open import Axolab.Category.Instances.Set
open import Axolab.Category.Functor
open import Axolab.Category.Functor.Bifunctor
open import Axolab.Data.Product
open import Axolab.Prelude

open Functor
open PropReasoning

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o ℓ} (C : Category o ℓ) where
  open Category C

  Hom_[-,-] : Bifunctor (C ^op) C (Set ℓ)
  F₀   Hom_[-,-] = λ where (A , B) → Hom A B
  F₁   Hom_[-,-] = λ where (f , h) g → h ∘ g ∘ f
  F-id Hom_[-,-] = funExt λ _ → id← ∘p id→
  F-∘  Hom_[-,-] (f , h) (i , j) = funExt λ p →
    (h ∘ j) ∘ p ∘ i ∘ f   ≡⟨ assoc← ⟩
    ((h ∘ j) ∘ p) ∘ i ∘ f ≡⟨ ap (_∘ i ∘ f) assoc→ ⟩
    (h ∘ j ∘ p) ∘ i ∘ f   ≡⟨ assoc→ ⟩
    h ∘ (j ∘ p) ∘ i ∘ f   ≡⟨ ap (h ∘_) assoc→ ⟩
    h ∘ j ∘ p ∘ i ∘ f     ≡⟨ ap (λ e → h ∘ j ∘ e) assoc← ⟩
    h ∘ j ∘ (p ∘ i) ∘ f   ≡⟨ ap (h ∘_) assoc← ⟩
    h ∘ (j ∘ p ∘ i) ∘ f   ∎

module _ {o ℓ o' ℓ'} (C : Category o ℓ) {D : Category o' ℓ'} (F : Functor D C) where
  private
    module C = Category C
    module D = Category D

    module F = Functor F

  Hom_[-,_-] : Functor (D ^op ×Cat C) (Set ℓ)
  F₀   Hom_[-,_-] = λ where (A , B) → C.Hom (F.₀ A) B
  F₁   Hom_[-,_-] = λ where (f , h) g → h C.∘ g C.∘ F.₁ f
  F-id Hom_[-,_-] = funExt λ g → C.id← ∘p (ap (_ C.∘_) F.F-id ∘p C.id→)
  F-∘  Hom_[-,_-] (f , h) (i , j) = funExt λ p →
    (h C.∘ j) C.∘ p C.∘ F.₁ (i D.∘ f)     ≡⟨ ap (λ e → _ C.∘ _ C.∘ e) (F.F-∘ i f) ⟩
    (h C.∘ j) C.∘ p C.∘ F.₁ i C.∘ F.₁ f   ≡⟨ C.assoc← ⟩
    ((h C.∘ j) C.∘ p) C.∘ F.₁ i C.∘ F.₁ f ≡⟨ ap (C._∘ F.₁ i C.∘ F.₁ f) C.assoc→ ⟩
    (h C.∘ j C.∘ p) C.∘ F.₁ i C.∘ F.₁ f   ≡⟨ C.assoc→ ⟩
    h C.∘ (j C.∘ p) C.∘ F.₁ i C.∘ F.₁ f   ≡⟨ ap (h C.∘_) C.assoc→ ⟩
    h C.∘ j C.∘ p C.∘ F.₁ i C.∘ F.₁ f     ≡⟨ ap (λ e → h C.∘ j C.∘ e) C.assoc← ⟩
    h C.∘ j C.∘ (p C.∘ F.₁ i) C.∘ F.₁ f   ≡⟨ ap (h C.∘_) C.assoc← ⟩
    h C.∘ (j C.∘ p C.∘ F.₁ i) C.∘ F.₁ f   ∎

open Category

Hom_[_,-] : ∀ {o ℓ} (C : Category o ℓ) → Ob C → Functor C (Set ℓ)
Hom C [ X ,-] = Right Hom C [-,-] X

Hom_[-,_] : ∀ {o ℓ} (C : Category o ℓ) → Ob C → Functor (C ^op) (Set ℓ)
Hom C [-, X ] = Left Hom C [-,-] X
