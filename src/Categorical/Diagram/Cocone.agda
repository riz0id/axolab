
open import Categorical.Category
open import Categorical.Functor

module Categorical.Diagram.Cocone
  {o ℓ o' ℓ'} {C : Category o ℓ} {J : Category o' ℓ'}
  (F : Functor J C)
  where

open import Prelude
open import Prelude.Equality

private
  open module C = Category C

  module J = Category J
  module F = Functor F

-- ---------------------------------------------------------------------------------------------------------------------

record Coapex (N : Ob) : Setoid (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  field
    ψ       : (X : J.Ob) → Hom (F.₀ X) N
    commute : {X Y : J.Ob} (f : J.Hom X Y) → ψ Y ∘ F.₁ f ≡ ψ X

record Cocone : Setoid (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  field
    {N}    : Ob
    coapex : Coapex N

  open Coapex coapex public
