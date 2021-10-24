module Prelude.Data.Product where

open import Prelude.Equality
open import Prelude.Primitive

private
  variable
    ℓ ℓ' : Level
    A B : Setoid ℓ
    C D : Setoid ℓ'

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _×_ _,_

record _×_ {ℓ ℓ'} (A : Setoid ℓ) (B : Setoid ℓ') : Setoid (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

×Path : {A×B C×D : A × B} → fst A×B ≡ fst C×D → snd A×B ≡ snd C×D → A×B ≡ C×D
×Path refl refl = refl
