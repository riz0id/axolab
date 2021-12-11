
open import Axolab.Category
open import Axolab.Category.Monad

module Axolab.Category.Instances.Kleisli
  {o ℓ} {C : Category o ℓ}
  (M : Monad C)
  where

open import Axolab.Category.Functor
open import Axolab.Prelude

open PropReasoning

private
  open module M = Monad C M

-- ---------------------------------------------------------------------------------------------------------------------

module _ where
  infixr 5 _∘K_

  open Category C

  _* : ∀ {X Y} (f : Hom X (M₀ Y)) → Hom (M₀ X) (M₀ Y)
  f * = μ _ ∘ M₁ f

  -- Kleisli composition
  _∘K_ : ∀ {X Y Z} (g : Hom Y (M₀ Z)) (g : Hom X (M₀ Y)) → Hom X (M₀ Z)
  g ∘K f = g * ∘ f

  id*← : ∀ {X Y} {f : Hom X (M₀ Y)} → η Y ∘K f ≡ f
  id*← {X} {Y} {f} =
    (μ Y ∘ M₁ (η Y)) ∘ f ≡⟨ ap (_∘ f) ident← ⟩
    id ∘ f               ≡⟨ id← ⟩
    f                    ∎

  id*→ : ∀ {X Y} {f : Hom X (M₀ Y)} → f ∘K η X ≡ f
  id*→ {X} {Y} {f} =
    (μ Y ∘ M₁ f) ∘ η X   ≡⟨ assoc→ ⟩
    μ Y ∘ M₁ f ∘ η X     ≡⟨ ap (_ ∘_) (sym (η-commutes X (M₀ Y) f)) ⟩
    μ Y ∘ η (M₀ Y) ∘ f   ≡⟨ assoc← ⟩
    (μ Y ∘ η (M₀ Y)) ∘ f ≡⟨ ap (_∘ f) ident→ ⟩
    id ∘ f               ≡⟨ id← ⟩
    f                        ∎

-- Kleisli : Category o ℓ
-- Kleisli = {!!}
-- Ob     Kleisli = C.Ob
-- Hom    Kleisli = λ X Y → C.Hom X (M₀ Y)
-- id     Kleisli = M.η _
-- _∘_    Kleisli = _∘K_
-- id←    Kleisli {X} {Y} {f} =
-- id→    Kleisli {X} {Y} {f} = id*→

-- assoc← Kleisli {X} {Y} {Z} {W} {f} {g} {h} =
--   (μ _ C.∘ M₁ h) C.∘ ((μ _ C.∘ M₁ g) C.∘ f) ≡⟨ {!!} ⟩
--   -- μ _ C.∘ M₁ h C.∘ ((μ _ C.∘ M₁ g) C.∘ f) ≡⟨ ap (μ _ C.∘_) C.assoc← ⟩
--   -- μ _ C.∘ (M₁ h C.∘ μ _ C.∘ M₁ g) C.∘ f ≡⟨ {!!} ⟩
--   -- μ _ C.∘ ((M₁ (μ _) C.∘ {!!}) C.∘ M₁ g) C.∘ f ≡⟨ ap (λ e → μ _ C.∘ ((M₁ _ C.∘ e) C.∘ M₁ g) C.∘ f) (sym {!μ-commutes!}) ⟩
--   -- μ _ C.∘ ((M₁ (μ _) C.∘ M₁ (M₁ h)) C.∘ M₁ g) C.∘ f ≡⟨ ap (λ e → μ _ C.∘ (e C.∘ M₁ g) C.∘ f) (sym (M-∘ _ _)) ⟩
--   -- μ _ C.∘ (M₁ (μ _ C.∘ M₁ h) C.∘ M₁ g) C.∘ f ≡⟨ ap (λ e → μ _ C.∘ e C.∘ f) (sym (M-∘ _ _)) ⟩
--   -- μ _ C.∘ M₁ ((μ _ C.∘ M₁ h) C.∘ g) C.∘ f    ≡⟨ C.assoc← ⟩
--   (μ _ C.∘ M₁ ((μ _ C.∘ M₁ h) C.∘ g)) C.∘ f  ∎
--   where
--     μ∘η*≡id : ∀ {X Y} {f : C.Hom X (M₀ Y)} → μ Y C.∘ (η (M₀ Y) C.∘ f) * ≡ f *
--     μ∘η*≡id {X} {Y} {f} =
--       μ Y C.∘ (η (M₀ Y) C.∘ f) * ≡⟨ {!!} ⟩
--       (C.id C.∘ f) * ≡⟨ {!!} ⟩
--       f * ∎
-- assoc→ Kleisli = {!!}
