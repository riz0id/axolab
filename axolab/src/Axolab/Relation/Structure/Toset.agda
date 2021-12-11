
open import Axolab.Prelude

module Axolab.Relation.Structure.Toset {o} (A : Set o) where

open import Axolab.Data.Bot
open import Axolab.Data.Coproduct
open import Axolab.Relation.Decidable
open import Axolab.Relation.Trichotomy

open import Axolab.Relation.Structure.Poset A
open import Axolab.Relation.Structure.Proset A

private
  variable
    x y z : A

-- ---------------------------------------------------------------------------------------------------------------------

record Toset (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality

  field
    poset : Poset ℓ

  open Poset poset public

  field
    total : (x y : A) → x ≤ y ∐ y ≤ x

record DecTotal (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality

  field
    toset : Toset ℓ

  open Toset toset public

  field
    decidable : (x y : A) → Dec (x ≤ y)

record StrictToset (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality

  field
    _<_     : A → A → Set ℓ
    trans<  : x < y → y < z → x < z
    compare : (x y : A) → Trichotomy (x < y) (x ≡ y) (y < x)

  field
    isSet   : (p q : x ≡ y) → p ≡ q
    isProp< : (p q : x < y) → p ≡ q

  -- _≤_ : A → A → Set (o ⊔ ℓ)
  -- x ≤ y = (x ≡ y) ∐ (x < y)

  _<?_ : (x y : A) → Dec (x < y)
  x <? y with compare x y
  ... | tri< x<y _ _ = because _ (of-yes x<y)
  ... | tri≈ x≮y _ _ = because _ (of-no  x≮y)
  ... | tri> x≮y _ _ = because _ (of-no  x≮y)

  -- proset : Proset (o ⊔ ℓ)
  -- Proset._~_        proset = _≤_
  -- Proset.reflexive~ proset = inl
  -- Proset.trans~     proset = {!!}
  -- Proset.isSet      proset = isSet
  -- Proset.isProp~    proset = {!!}

  -- poset : Poset (o ⊔ ℓ)
  -- Poset.proset   poset = proset
  -- Poset.antisym≤ poset = {!!}

  -- toset : Toset (o ⊔ ℓ)
  -- Toset.poset toset = poset
  -- Toset.total toset = {!!}
