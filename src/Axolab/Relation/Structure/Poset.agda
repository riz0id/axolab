
open import Axolab.Prelude

module Axolab.Relation.Structure.Poset {o} (A : Set o) where

open import Axolab.Relation.Structure.Proset A

private
  variable
    x y z : A

-- ---------------------------------------------------------------------------------------------------------------------

record Poset (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality
  field
    proset : Proset ℓ

  open module proset = Proset proset public
    renaming ( _~_ to _≤_
             ; reflexive~ to reflexive≤; refl~ to refl≤; trans~ to trans≤
             ; resp~/← to resp≤/←; resp~/→ to resp≤/→
             ; id~/← to id≤/←; id~/→ to id≤/→; assoc~/← to assoc≤/←; assoc~/→ to assoc≤/→ )

  field
    antisym≤ : x ≤ y → y ≤ x → x ≡ y
