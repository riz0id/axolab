
open import Categorical.Category
open import Categorical.Category.Structure.Cocartesian

module Categorical.Monad.Ideal
  {o ℓ} {C : Category o ℓ}
  (co : Cocartesian C)
  where

open import Categorical.Functor
open import Categorical.Monad.Core C
open import Categorical.NaturalTransformation
open import Prelude

open Category C
open Cocartesian co
open Functor

-- ---------------------------------------------------------------------------------------------------------------------

record Ideal : Setoid (o ⊔ ℓ) where
  field
    T : Endofunctor C
    μ : {!-+- !} ⇒ T
