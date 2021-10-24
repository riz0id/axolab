module Categorical.Functor.Instances.Hom where

open import Categorical.Category
open import Categorical.Category.Instances.Product
open import Categorical.Category.Instances.Sets
open import Categorical.Functor
open import Categorical.Bifunctor
open import Prelude
open import Prelude.Equality
open import Prelude.Data.Product

-- ---------------------------------------------------------------------------------------------------------------------

open Functor
open _×_

module _ {o ℓ} {C : Category o ℓ} where
  private open module C = Category C
  open import Categorical.Solver.Associativity C

  Hom[-,-] : Bifunctor (C ^op) C (Sets ℓ)
  F₀   Hom[-,-] (X , Y)   = Hom X Y
  F₁   Hom[-,-] (f , g) h = g ∘ h ∘ f
  F-id Hom[-,-] = funExt λ f → id← _ ∘p id→ _
  F-∘  Hom[-,-] (f , h) (i , j) = funExt λ p →
    associate refl
      ∥ ((⟦ h ⟧ ∙ ⟦ j ⟧) ∙ ⟦ p ⟧ ∙ ⟦ i ⟧ ∙ ⟦ f ⟧)
      ∥ (⟦ h ⟧ ∙ (⟦ j ⟧ ∙ ⟦ p ⟧ ∙ ⟦ i ⟧) ∙ ⟦ f ⟧)

  Hom[_,-] : C.Ob → Functor C (Sets ℓ)
  Hom[ X ,-] = Right Hom[-,-] X
