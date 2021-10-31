
open import Categorical.Category

module Categorical.Functor.Instances.Point {o ℓ} (C : Category o ℓ) where

open import Categorical.Category.Instances.Sets
open import Categorical.Functor
open import Prelude
open import Prelude.Equality

open Category (C ^op)

-- ---------------------------------------------------------------------------------------------------------------------

data Pt : Setoid o where
  pt : Ob → Pt

pt₀ : Ob → Functor (C ^op) (Sets ℓ)
Functor.F₀   (pt₀ X) Y = Lift {_} {ℓ} (Hom X Y)
Functor.F₁   (pt₀ X) f (lift g) = lift (f ∘ g)
Functor.F-id (pt₀ X) = funExt (λ _ → ap lift id←)
Functor.F-∘  (pt₀ X) f _ = funExt λ where
  (lift f) → ap lift assoc→
