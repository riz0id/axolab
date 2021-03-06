
module Axolab.Category.Core where

open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

infixl 60 _^op

record Category (o ℓ : Level) : Set (lsuc (o ⊔ ℓ)) where
  eta-equality
  infixr 9 _∘_

  field
    Ob  : Set o
    Hom : Ob → Ob → Set ℓ

  field
    id  : {X : Ob} → Hom X X
    _∘_ : {X Y Z : Ob} → Hom Y Z → Hom X Y → Hom X Z

  field
    id← : {X Y : Ob} {f : Hom Y X} → id ∘ f ≡ f
    id→ : {X Y : Ob} {f : Hom X Y} → f ∘ id ≡ f

  field
    assoc← : {X Y Z W : Ob} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z W} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    assoc→ : {X Y Z W : Ob} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z W} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

open Category

_^op : {o ℓ : Level} → Category o ℓ → Category o ℓ
Ob     (C ^op) = Ob C
Hom    (C ^op) = λ X Y → Hom C Y X
id     (C ^op) = id C
_∘_    (C ^op) = λ f g → _∘_ C g f
id←    (C ^op) = id→ C
id→    (C ^op) = id← C
assoc← (C ^op) {h = h} = assoc→ C {f = h}
assoc→ (C ^op) {h = h} = assoc← C {f = h}
