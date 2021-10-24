open import Categorical.Category

module Categorical.Category.Structure.Monoidal {o ℓ} (C : Category o ℓ) where

open import Categorical.Functor
open import Categorical.Bifunctor
open import Categorical.Morphism.Isomorphism C
open import Prelude
open import Prelude.Equality
open import Prelude.Data.Product

private
  open module C = Category C
  open Commutation C

-- ---------------------------------------------------------------------------------------------------------------------

record Monoidal : Setoid (o ⊔ ℓ) where
  infixr 5 _⨂₀_ _⨂₁_

  field
    ⨂    : Bifunctor C C C
    unit : Ob

  open module ⨂ = Functor ⨂

  _⨂₀_ : Ob → Ob → Ob
  _⨂₀_ = biap ⨂

  _⨂₁_ : {X Y Z W : Ob} → Hom X Y → Hom Z W → Hom (X ⨂₀ Z) (Y ⨂₀ W)
  f ⨂₁ g = F₁ (f , g)

  -⨂_ : Ob → Endofunctor C
  -⨂_ = Right ⨂

  _⨂- : Ob → Endofunctor C
  _⨂- = Left ⨂

  field
    unitor←    : {X : Ob} → (unit ⨂₀ X) ≅ X
    unitor→    : {X : Ob} → (X ⨂₀ unit) ≅ X
    associator : {X Y Z : Ob} → (X ⨂₀ Y) ⨂₀ Z ≅ X ⨂₀ (Y ⨂₀ Z)

  -- Mnemonic device on unit morphism:
  --
  -- * Double arrow to indicate if moving to a unit⇐, or from a unit⇒id
  -- * Single arrow to indicate if the unit is on the left← side of the tensor, or the right→.
  --
  open module unitor← {X} = Isomorphism (unitor← {X}) public
    renaming ( from to unit⇒id←   -- unit ⨂₀ X → X
             ; to   to unit⇐id← ) -- X → unit ⨂₀ X
  open module unitor→ {X} = Isomorphism (unitor→ {X}) public
    renaming ( from to unit⇒id→   -- X ⨂₀ unit → X
             ; to   to unit⇐id→ ) -- X → X ⨂₀ unit

  open module associator {X} {Y} {Z} = Isomorphism (associator {X} {Y} {Z}) public
    renaming ( from to assoc→⨂   -- (X ⨂₀ Y) ⨂₀ Z → X ⨂₀ (Y ⨂₀ Z)
             ; to   to assoc←⨂ ) -- X ⨂₀ (Y ⨂₀ Z) → (X ⨂₀ Y) ⨂₀ Z

  field
    unitor←commute : {X Y : Ob} {f : Hom X Y} → unit⇒id← ∘ (C.id ⨂₁ f) ≡ f ∘ unit⇒id←
    unitor→commute : {X Y : Ob} {f : Hom X Y} → unit⇒id→ ∘ (f ⨂₁ C.id) ≡ f ∘ unit⇒id→

    assoc-commute : {X Y Z W : Ob} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z W} →
      assoc→⨂ ∘ ((f ⨂₁ g) ⨂₁ h) ≡ (f ⨂₁ (g ⨂₁ h)) ∘ assoc→⨂

    triangle : {X Y : Ob} →
      [ (X ⨂₀ unit) ⨂₀ Y ⇒ X ⨂₀ Y ]⟨
        assoc→⨂          ⇒⟨ X ⨂₀ (unit ⨂₀ Y) ⟩
        C.id ⨂₁ unit⇒id←
      ≡ unit⇒id→ ⨂₁ C.id
      ⟩

    pentagon : {X Y Z W : Ob} →
      [ ((X ⨂₀ Y) ⨂₀ Z) ⨂₀ W ⇒ X ⨂₀ (Y ⨂₀ (Z ⨂₀ W)) ]⟨
        assoc→⨂ ⨂₁ C.id ⇒⟨ (X ⨂₀ Y ⨂₀ Z) ⨂₀ W ⟩
        assoc→⨂         ⇒⟨ X ⨂₀ (Y ⨂₀ Z) ⨂₀ W ⟩
        C.id ⨂₁ assoc→⨂
      ≡ assoc→⨂         ⇒⟨ (X ⨂₀ Y) ⨂₀ Z ⨂₀ W ⟩
        assoc→⨂
      ⟩
