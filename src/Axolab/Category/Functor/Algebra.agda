
open import Axolab.Category

module Axolab.Category.Functor.Algebra {o ℓ} (C : Category o ℓ) where

open import Axolab.Category.Functor
open import Axolab.Prelude

open Category C

private
  variable
    X Y : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Algebra (F : Endofunctor C) : Setoid (o ⊔ ℓ) where
  private
    module F = Functor F

  field
    U   : Ob
    alg : Hom (F.₀ U) U

record Homomorphism {H : Endofunctor C} (F G : Algebra H) : Setoid (o ⊔ ℓ) where
  private
    module H = Functor H

    module F = Algebra F
    module G = Algebra G

  field
    homo     : Hom F.U G.U
    commutes : homo ∘ F.alg ≡ G.alg ∘ H.₁ homo
