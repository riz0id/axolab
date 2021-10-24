module Categorical.Bifunctor.Instances.Product where

open import Categorical.Category
open import Categorical.Category.Instances.Product
open import Categorical.Category.Instances.Sets
open import Categorical.Functor
open import Categorical.Bifunctor
open import Prelude.Data.Product
open import Prelude
open import Prelude.Equality

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o : Level} where
  open Category
  open Functor

  Product : Bifunctor (Sets o) (Sets o) (Sets o)
  F₀   Product (A , B)   = A × B
  F₁   Product (f , g) x = f (fst x) , g (snd x)
  F-id Product           = refl
  F-∘  Product g f       = refl
