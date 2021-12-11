
open import Axolab.Prelude

module Axolab.Relation.Structure.Lattice {o} (A : Set o) where

open import Axolab.Relation.Structure.Poset A

private
  variable
    x y z : A

-- ---------------------------------------------------------------------------------------------------------------------

record JoinSemilattice (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality

  field
    poset : Poset ℓ

  open Poset poset public

  field
    ⊥   : A
    _∨_ : A → A → A


record Lattice (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality

  field
    poset : Poset ℓ

  open Poset poset public

  field
    ⊤   : A
    _∧_ : A → A → A

  -- field
  --   comm∧  : x ∧ y ≡ y ∧ x
  --   assoc∧ : (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)

  -- field
  --   sup←   : x ≤ (x ∨ y)
  --   sup→   : y ≤ (x ∨ y)
  --   comm∨  : x ∨ y ≡ y ∨ x
  --   assoc∨ : (x ∨ y) ∨ z ≡ x ∨ (y ∨ z)
