
module Axolab.Type where

open import Agda.Primitive public
  renaming ( Set to Type; Setω to Typeω )
  using    ( Level; lsuc; lzero; _⊔_ )

-- ---------------------------------------------------------------------------------------------------------------------

record Lift {ℓ ℓ'} (A : Type ℓ) : Type (ℓ ⊔ ℓ') where
  constructor lift
  field
    lower : A
