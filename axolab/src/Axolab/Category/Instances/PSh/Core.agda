
open import Axolab.Category

module Axolab.Category.Instances.PSh.Core {o ℓ} (C : Category o ℓ) where

open import Axolab.Category.Functor
open import Axolab.Category.Instances.Functors
open import Axolab.Category.Instances.Set
open import Axolab.Category.Functor.Adjoint
open import Axolab.Category.NaturalTransformation
open import Axolab.Prelude

open Category C
open Functor
open NaturalTransformation

-- ---------------------------------------------------------------------------------------------------------------------

PSh : (ℓ' : Level) → Category _ _
PSh ℓ' = Functors (C ^op) (Set (lsuc (o ⊔ ℓ')))

module _ {ℓ' : Level} where

  よ₀ : Ob → Functor (C ^op) (Set (ℓ ⊔ ℓ'))
  F₀   (よ₀ Y) X   = Lift {ℓ' = ℓ'} (Hom X Y)
  F₁   (よ₀ Y) f g = lift (unlift g ∘ f)
  F-id (よ₀ _)     = funExt λ where (lift f) → ap lift (id→ {f = f})
  F-∘  (よ₀ _) _ _ = funExt λ where (lift f) → ap lift assoc←

  Embed : Functor C (Functors (C ^op) (Set (ℓ ⊔ ℓ')))
  F₀   Embed            = よ₀
  F₁   Embed f .η       = λ _ map → lift (f ∘ unlift map)
  F₁   Embed f .natural = λ _ _ _ → funExt λ _ → ap lift assoc←
  F-id Embed            = NT≡ (funExt λ _ → funExt λ _ → ap lift id←)
  F-∘  Embed _ _        = NT≡ (funExt λ _ → funExt λ _ → ap lift assoc→)

  ev : Ob → Functor (PSh ℓ') (Set _)
  F₀   (ev c) x   = F₀ x c 
  F₁   (ev c) f g = η f c g
  F-id (ev c)     = refl
  F-∘  (ev c) f g = refl
