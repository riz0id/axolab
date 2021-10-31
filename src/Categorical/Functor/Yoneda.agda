
module Categorical.Functor.Yoneda where

open import Categorical.Category
open import Categorical.Category.Structure.Cartesian
open import Categorical.Category.Instances.Functors
open import Categorical.Category.Instances.Sets
open import Categorical.Functor
open import Categorical.Functor.Hom
open import Categorical.NaturalTransformation
open import Prelude
open import Prelude.Data.Product
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o ℓ} (C : Category o ℓ) where
  open Category C
  open Functor

  postulate
    -- Hom[-,A]-∘ : {X Y Z : Ob} (g : Hom Y Z) (f : Hom X Y)
    --   → Hom[-,A]⇒Hom[-,B] C (g ∘ f) ≡ (Hom[-,A]⇒Hom[-,B] C g ∘⇑ Hom[-,A]⇒Hom[-,B] C f)

  postulate embed : Functor C (Functors (C ^op) (Sets (o ⊔ lsuc ℓ)))
  -- F₀   embed         = Hom[ C ][-,_]
  -- F₁   embed         = Hom[-,A]⇒Hom[-,B] C
  -- F-id embed {X = X} = Hom[-,id]⇒id-η C {X}
  -- F-∘  embed         = Hom[-,A]-∘

  postulate
    yoneda-inverse← : (A : Ob) → (PSh : Functor (C ^op) (Sets (o ⊔ lsuc ℓ)))
      → Functor.F₀ Hom[ Functors (C ^op) (Sets ℓ) ][-, PSh ] PSh ≡ {!Functor.F₀ PSh A!}
      --Functor.F₀ PSh A


module _ {o ℓ} {C : Category o ℓ} (ca : Cartesian C) where
  open import Categorical.Functor.Instances.Point C
  open Category C
  open PropReasoning

  theorem : {X A B : Ob}
    → (π₁ f : Hom X A)
    → (π₂ g : Hom X B)
    → (π₁ ≡ f) × (π₂ ≡ g)
  theorem π₁ f π₂ g =
    {!!}
    where
      π₁≡f : π₁ ≡ f
      π₁≡f = {!!}

      π₂≡g : π₂ ≡ g
      π₂≡g = {!!}
