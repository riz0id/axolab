module Categorical.NaturalTransformation.NaturalIsomorphism where

open import Categorical.Category
open import Categorical.Functor
open import Categorical.NaturalTransformation.Core
open import Categorical.Morphism.Isomorphism
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

open Isomorphism

module _ {o ℓ o' ℓ'} {C : Category o ℓ} {D : Category o' ℓ'} where
  private
    module C = Category C
    module D = Category D

  record NaturalIsomorphism (F G : Functor C D) : Setoid (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    eta-equality
    private
      module F = Functor F
      module G = Functor G

    field
      F⇒G : NaturalTransformation F G
      F⇐G : NaturalTransformation G F

    module ⇒ = NaturalTransformation F⇒G
    module ⇐ = NaturalTransformation F⇐G

    field
      niso← : (X : C.Ob) → ⇐.η X D.∘ ⇒.η X ≡ D.id
      niso→ : (X : C.Ob) → ⇒.η X D.∘ ⇐.η X ≡ D.id

    F₀≅G₀ : {X : C.Ob} → Isomorphism D (F.₀ X) (G.₀ X)
    from F₀≅G₀ = ⇒.η _
    to   F₀≅G₀ = ⇐.η _
    iso← F₀≅G₀ = niso← _
    iso→ F₀≅G₀ = niso→ _
