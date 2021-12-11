-- Extension of ordered sets by a maximal element
--

module Axolab.Relation.Order.Infinity where

open import Axolab.Relation.Structure.Proset
open import Axolab.Relation.Structure.Poset
open import Axolab.Relation.Structure.Toset
open import Axolab.Prelude
open import Axolab.Prelude.Function

private
  variable
    o ℓ : Level

-- ---------------------------------------------------------------------------------------------------------------------

record Set∞ (o ℓ : Level) : Set (lsuc (o ⊔ ℓ)) where
  field
    set : Set o
    _≤_ : set → set → Set ℓ

data _∞ (A : Set∞ o ℓ) : Set o where
  inf : A ∞
  fin : Set∞.set A → A ∞

module _ {o ℓ} {A : Set∞ o ℓ} where
  infix 5 _≼∞_

  private
    open module A = Set∞ A

  data _≼∞_ : A ∞ → A ∞ → Set (o ⊔ ℓ) where
    inf : {x : A ∞} → x ≼∞ inf
    inc : {x y : set} → x ≤ y → fin x ≼∞ fin y

module _ {o ℓ} {U : Set o} (proset : Proset U ℓ) where
  private
    A = record { set = U; _≤_ = Proset._~_ proset }

    open module proset = Proset proset
    open module A      = Set∞ A

  _∪∞-Proset : Proset (A ∞) (o ⊔ ℓ)
  Proset._~_        _∪∞-Proset = _≼∞_
  Proset.reflexive~ _∪∞-Proset = reflexive≼ _ _ where
    reflexive≼ : (x y : A ∞) → x ≡ y → x ≼∞ y
    reflexive≼ inf     ._ refl = inf
    reflexive≼ (fin _) ._ refl = inc (reflexive~ refl)
  Proset.trans~     _∪∞-Proset = trans≼ where
    trans≼ : {x y z : A ∞} → x ≼∞ y → y ≼∞ z → x ≼∞ z
    trans≼ _         inf       = inf
    trans≼ (inc x≤y) (inc y≤z) = inc (trans~ x≤y y≤z)
  Proset.isSet      _∪∞-Proset = λ where refl refl → refl
  Proset.isProp~    _∪∞-Proset = isProp≼ where
    isProp≼ : {x y : A ∞} (p q : x ≼∞ y) → p ≡ q
    isProp≼ inf     inf     = refl
    isProp≼ (inc p) (inc q) = ap inc (isProp~ p q)

module _ {o ℓ} {U : Set o} (poset : Poset U ℓ) where
  private
    A = record { set = U; _≤_ = Poset._≤_ poset }

    open module proset  = Poset  poset
    open module proset∞ = Proset proset
    open module A       = Set∞ A

  _∪∞-Poset : Poset (A ∞) (o ⊔ ℓ)
  Poset.proset   _∪∞-Poset = proset ∪∞-Proset
  Poset.antisym≤ _∪∞-Poset = antisym≼ where
    antisym≼ : {x y : A ∞} → x ≼∞ y → y ≼∞ x → x ≡ y
    antisym≼ inf       inf       = refl
    antisym≼ (inc x≤y) (inc y≤x) = ap fin (antisym≤ x≤y y≤x)


  -- infix 5 _≼∞_


  -- _+∞-Proset : Poset set ℓ → Proset (A ∞) (o ⊔ ℓ)
  -- P +∞-Proset = record
  --   { _~_        = _≼∞_
  --   ; reflexive~ = {!!}
  --   ; trans~     = {!!}
  --   ; isSet      = {!!}
  --   ; isProp~    = {!!}
  --   }
  --   where
  --     reflexive≼∞ :
