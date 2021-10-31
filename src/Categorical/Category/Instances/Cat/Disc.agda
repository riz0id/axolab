
module Categorical.Category.Instances.Cat.Disc where

open import Categorical.Category
open import Categorical.Category.Instances.Cat.Cat
open import Categorical.Category.Instances.Sets
open import Categorical.Functor
open import Categorical.Functor.Adjoint
open import Categorical.NaturalTransformation
open import Prelude
open import Prelude.Equality

open Adjoint
open Category
open Functor
open NaturalTransformation

-- ---------------------------------------------------------------------------------------------------------------------

Obj : {o ℓ : Level} → Functor (Cat o ℓ) (Sets o)
F₀   Obj = Ob
F₁   Obj = F₀
F-id Obj = refl
F-∘  Obj = λ _ _ → refl

Disc : (o ℓ : Level) → Functor (Sets o) (Cat o (o ⊔ ℓ))
F₀   (Disc o ℓ) S .Ob     = S
F₀   (Disc o ℓ) S .Hom    = λ X Y → Lift {ℓ' = ℓ} (X ≡* Y)
F₀   (Disc o ℓ) S .id     = lift refl
F₀   (Disc o ℓ) S ._∘_    = λ where (lift refl) (lift refl) → lift refl
F₀   (Disc o ℓ) S .id←    = ap lift (UIP _ _)
F₀   (Disc o ℓ) S .id→    = ap lift (UIP _ _)
F₀   (Disc o ℓ) S .assoc← = ap lift (UIP _ _)
F₀   (Disc o ℓ) S .assoc→ = ap lift (UIP _ _)
F₁   (Disc o ℓ) S .F₀ X    = S X
F₁   (Disc o ℓ) S .F₁      = λ where (lift X) → lift (ap S X)
F₁   (Disc o ℓ) S .F-id    = ap lift (UIP _ _)
F₁   (Disc o ℓ) S .F-∘ _ _ = ap lift (UIP _ _)
F-id (Disc o ℓ) = Functor≡ refl λ where (lift refl) → refl
F-∘  (Disc o ℓ) _ _ = Functor≡ refl λ where (lift refl) → refl

Disc⊣Obj : {o ℓ : Level} → Disc o ℓ ⊣ Obj
unit   Disc⊣Obj .η       = λ _ x → x
unit   Disc⊣Obj .natural = λ _ _ _ → refl
counit Disc⊣Obj .η       = λ C → record
  { F₀   = λ x → x
  ; F₁   = λ where (lift refl) → id C
  ; F-id = refl
  ; F-∘  = λ where (lift refl) (lift refl) → sym (id→ C)
  }
counit Disc⊣Obj .natural = λ _ _ f → Functor≡ refl λ where (lift refl) → sym (F-id f)
zip    Disc⊣Obj = Functor≡ refl λ where (lift refl) → refl
zag    Disc⊣Obj = refl
