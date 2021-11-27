
open import Axolab.Category
open import Axolab.Category.Structure.Cartesian

module Theorem.ProductRepresentation {o ℓ} (D : Category o ℓ) (Ca : Cartesian D) where

open import Axolab.Category.Functor
open import Axolab.Category.Instances.PSh D
open import Axolab.Category.Instances.Set
open import Axolab.Data.Product
open import Axolab.Prelude

open Category
open Cartesian Ca
open Functor
open PropReasoning

private
  module D = Category D
  module PSh = Category (PSh ℓ)
  module よ₀ (A : D.Ob) = Functor (よ₀ {ℓ} A)

-- ---------------------------------------------------------------------------------------------------------------------

proj₁ : ∀ {ℓ} {A B : Set ℓ} → A × B → A
proj₁ = fst

embed× : (A B : D.Ob) → Functor (D ^op) (Set ℓ)
embed× A B = よ₀ {ℓ} (A ×₀ B)

lemma-pi₁ : {A B : D.Ob} (f : Hom D (A ×₀ B) A) (g : Hom D (A ×₀ B) B)
  → F₁ (よ₀ {ℓ} (A ×₀ B)) (f ×₁ g) ≡ λ where h → lift (unlift h D.∘ (π₁ ×₁ π₂))
lemma-pi₁ {A} {B} f g = {!!}
  -- funExt λ where
  -- (lift h) →
  --   lift (h D.∘ (f ×₁ g))  ≡⟨ ap (λ e → lift (h D.∘ e)) p ⟩
  --   lift (h D.∘ (π₁ ×₁ π₂)) ∎
  --   where
  --     pi1 : π₁ ≡ π₁ D.∘ (f ×₁ g)
  --     pi1 = π₁                ≡⟨ sym D.id→ ⟩
  --           π₁ D.∘ D.id       ≡⟨ {!ap (π₁ D.∘_) (sym π₁×π₂≡id!} ⟩
  --           π₁ D.∘ (π₁ ×₁ π₂) ≡⟨ {!!} ⟩
  --           π₁ D.∘ (f ×₁ g)   ∎

  --     p : f ×₁ g ≡ π₁ ×₁ π₂
  --     p = ×-unique
  --       {!!}
  --       {!!}



      -- sym (×-unique (subst (_≡ π₁ D.∘ (π₁ ×₁ π₂)) {!!} (sym π₁×₁≡id)) {!!})
      -- f  ×₁ g  ≡⟨ {!sym (×-unique₂ ? ?)!} ⟩
      --     D.id     ≡⟨ sym π₁×π₂≡id ⟩
      --     π₁ ×₁ π₂ ∎
