
module Axolab.Algebra.Theory.Instances.Tree where

open import Axolab.Category
open import Axolab.Algebra.Theory
open import Axolab.Algebra.Theory.Instances.List
open import Axolab.Algebra.Theory.Structure.Monoid
open import Axolab.Prelude
open import Axolab.Prelude.Primitive.Vect using (_∷_; nil)

open Interpretation
open Model

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _⋉_

record Tree {o} (A : Setoid o) : Setoid o where
  inductive
  constructor _⋉_

  field
    root   : A
    leaves : List (Tree A)

Forest : {o : Level} → Setoid o → Setoid o
Forest A = List (Tree A)

leaf : ∀ {o} {A : Setoid o} → A → Tree A
leaf x = x ⋉ nil
