
module Categorical.Functor.Hom where

open import Categorical.Bifunctor
open import Categorical.Category
open import Categorical.Category.Instances.Sets
open import Categorical.Functor
open import Categorical.NaturalTransformation
open import Prelude
open import Prelude.Equality
open import Prelude.Data.Product

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o ℓ} (C : Category o ℓ) where
  open Category C
  open Functor

  open PropReasoning


  postulate Hom[_][-,-] : Bifunctor (C ^op) C (Sets (lsuc ℓ))

  -- TODO!
  -- F₀   Hom[_][-,-] (A , B)   = Hom A B
  -- F₁   Hom[_][-,-] (f , g) h = g ∘ h ∘ f
  -- F-id Hom[_][-,-] = funExt λ f →
  --   id ∘ f ∘ id ≡⟨ ap (λ e → id ∘ e) id→ ⟩
  --   id ∘ f      ≡⟨ id← ⟩
  --   f           ∎
  -- F-∘  Hom[_][-,-] (f₁ , f₂) (g₁ , g₂) = funExt λ where
  --   h → F₀ {!f₂!} {!!} ≡⟨ {!!} ⟩
  --       F₀ {!!} {!!} ∎

  -- Hom[_][_,-] : Ob → Functor C (Sets (o ⊔ ℓ))
  -- Hom[_][_,-] A = Right Hom[_][-,-] A

  Hom[_][-,_] : Ob → Functor (C ^op) (Sets (lsuc ℓ))
  Hom[_][-,_] A = Left Hom[_][-,-] A

  -- TODO!
  postulate
    -- Hom[-,A]⇒Hom[-,B] : {A B : Ob} → Hom A B → NaturalTransformation (Hom[_][-,_] A) (Hom[_][-,_] B)

    -- Hom[-,id]⇒id-η : {A : Ob} → Hom[-,A]⇒Hom[-,B] {A = A} id ≡ idNT
