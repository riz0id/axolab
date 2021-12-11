
open import Axolab.Prelude

module Axolab.Relation.Structure.Poset {o} (A : Set o) where

open import Axolab.Data.Bot
open import Axolab.Relation.Decidable

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
             ; reflexive~ to reflexive≤; refl~ to refl≤; trans~ to trans≤; isProp~ to isProp≤
             ; resp~/← to resp≤/←; resp~/→ to resp≤/→
             ; id~/← to id≤/←; id~/→ to id≤/→; assoc~/← to assoc≤/←; assoc~/→ to assoc≤/→ )

  field
    antisym≤ : x ≤ y → y ≤ x → x ≡ y

record StrictPoset (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality
  infix 6 _<_

  field
    _<_   : A → A → Set ℓ
    isSet : (p q : x ≡ y) → p ≡ q

  field
    irrefl< : x ≡ y → x < y → ⊥
    trans<  : x < y → y < z → x < z
    isProp< : (p q : x < y) → p ≡ q

  resp< : {x' y' : A} → x ≡ x' → y ≡ y' → x < y → x' < y'
  resp< refl refl x<y = x<y

  resp</← : {x' : A} → x ≡ x' → x < y → x' < y
  resp</← x≡x' x<y = resp< x≡x' refl x<y

  resp</→ : {y' : A} → y ≡ y' → x < y → x < y'
  resp</→ y≡y' x<y = resp< refl y≡y' x<y

record DecPoset (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality

  field
    poset : Poset ℓ

  open Poset poset

  field
    decidable : (x y : A) → Dec (x ≤ y)

module PosetReasoning {ℓ} (poset : Poset ℓ) where
  open module poset = Poset poset

  infixr 0 _≤⟨_⟩_
  infix  1 _∎

  _≤⟨_⟩_ : (x : A) {y z : A} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ p ⟩ q = trans≤ p q

  _∎ : (x : A) → x ≤ x
  x ∎ = refl≤
