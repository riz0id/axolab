
open import Axolab.Prelude
open import Axolab.Relation.Structure.Poset

module Axolab.Algebra.Structure.Lattice
  {o ℓ} {A : Set o}
  (poset : Poset A ℓ)
  where

private
  variable
    x y z w : A

-- ---------------------------------------------------------------------------------------------------------------------

record Lattice : Set (o ⊔ ℓ) where
  eta-equality
  infixr 7 _∧_
  infixr 6 _∨_

  field
    ⊤   : A
    _∧_ : A → A → A

    id∧/←    : x ∧ ⊤ ≡ x
    id∧/→    : ⊤ ∧ x ≡ x
    assoc∧/← : x ∧ y ∧ z ≡ (x ∧ y) ∧ z
    comm∧    : x ∧ y ≡ y ∧ x
    idem∧    : x ∧ x ≡ x


  assoc∧/→ : (x ∧ y) ∧ z ≡ x ∧ y ∧ z
  assoc∧/→ = sym assoc∧/←

  field
    _∨_ : A → A → A

    id∨/←    : x ∧ ⊤ ≡ x
    id∨/→    : ⊤ ∧ x ≡ x
    assoc∨/← : x ∨ y ∨ z ≡ (x ∨ y) ∨ z
    comm∨    : x ∨ y ≡ y ∨ x
    idem∨    : x ∨ x ≡ x

  assoc∨/→ : (x ∨ y) ∨ z ≡ x ∨ y ∨ z
  assoc∨/→ = sym assoc∨/←

  field
    ∧absorb∨ : x ∧ (y ∨ z) ≡ x
    ∨absorb∧ : x ∨ (y ∧ z) ≡ x
