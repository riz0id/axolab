
module Axolab.Data.Product where

open import Axolab.Prelude

private
  variable
    ℓ ℓ' : Level
    A B : Set ℓ
    C D : Set ℓ'

-- ---------------------------------------------------------------------------------------------------------------------

infix  2 Σ
infixr 6 _×_ _,_

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

Σ-Path : {B : A → Set ℓ'} {x y : Σ A B} → (p : Σ.fst x ≡ Σ.fst y) → subst B p (Σ.snd x) ≡ Σ.snd y → x ≡ y
Σ-Path refl refl = refl

record _×_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

×Path : {A×B C×D : A × B} → fst A×B ≡ fst C×D → snd A×B ≡ snd C×D → A×B ≡ C×D
×Path refl refl = refl
