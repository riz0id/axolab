
open import Axolab.Category

module Axolab.Category.Structure.Monoidal {o ℓ} (C : Category o ℓ) where

open import Axolab.Category.Functor
open import Axolab.Category.Functor.Bifunctor
open import Axolab.Category.Morphism C
open import Axolab.Data.Product
open import Axolab.Prelude

open Category C
open Commutation C

private
  variable
    X Y Z W : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Monoidal : Set (o ⊔ ℓ) where
  infixr 5 _⨂₀_ _⨂₁_

  field
    ⨂    : Bifunctor C C C
    unit : Ob

  open module ⨂ = Functor ⨂

  _⨂₀_ : Ob → Ob → Ob
  _⨂₀_ = biap ⨂

  _⨂₁_ : Hom X Y → Hom Z W → Hom (X ⨂₀ Z) (Y ⨂₀ W)
  f ⨂₁ g = F₁ (f , g)

  -⨂_ : Ob → Endofunctor C
  -⨂_ = Right ⨂

  _⨂- : Ob → Endofunctor C
  _⨂- = Left ⨂

  field
    unitor←    : unit ⨂₀ X ≅ X
    unitor→    : X ⨂₀ unit ≅ X
    associator : (X ⨂₀ Y) ⨂₀ Z ≅ X ⨂₀ (Y ⨂₀ Z)

  open module unitor← {X} = Isomorphism (unitor← {X}) public
    renaming ( from to unit⇒id←   -- unit ⨂₀ X → X
             ; to   to unit⇐id← ) -- X → unit ⨂₀ X
  open module unitor→ {X} = Isomorphism (unitor→ {X}) public
    renaming ( from to unit⇒id→   -- X ⨂₀ unit → X
             ; to   to unit⇐id→ ) -- X → X ⨂₀ unit

  open module associator {X Y Z} = Isomorphism (associator {X} {Y} {Z}) public
    renaming ( from to assoc→⨂   -- (X ⨂₀ Y) ⨂₀ Z → X ⨂₀ (Y ⨂₀ Z)
             ; to   to assoc←⨂ ) -- X ⨂₀ (Y ⨂₀ Z) → (X ⨂₀ Y) ⨂₀ Z

  field
    triangle : {X Y : Ob} →
      [ (X ⨂₀ unit) ⨂₀ Y ⇒ X ⨂₀ Y ]⟨
        assoc→⨂          ⇒⟨ X ⨂₀ (unit ⨂₀ Y) ⟩
        id ⨂₁ unit⇒id←
      ≡ unit⇒id→ ⨂₁ id
      ⟩

    pentagon : {X Y Z W : Ob} →
      [ ((X ⨂₀ Y) ⨂₀ Z) ⨂₀ W ⇒ X ⨂₀ (Y ⨂₀ (Z ⨂₀ W)) ]⟨
        assoc→⨂ ⨂₁ id ⇒⟨ (X ⨂₀ Y ⨂₀ Z) ⨂₀ W ⟩
        assoc→⨂       ⇒⟨ X ⨂₀ (Y ⨂₀ Z) ⨂₀ W ⟩
        id ⨂₁ assoc→⨂
      ≡ assoc→⨂       ⇒⟨ (X ⨂₀ Y) ⨂₀ Z ⨂₀ W ⟩
        assoc→⨂
      ⟩
