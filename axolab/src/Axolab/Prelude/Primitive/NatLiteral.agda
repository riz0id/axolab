
module Axolab.Prelude.Primitive.NatLiteral where

open import Agda.Builtin.Nat
open import Axolab.Data.Top
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

record NatLiteral {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    constraint : Nat → Set ℓ
    natlit     : (n : Nat) {{_ : constraint n}} → A

open NatLiteral {{...}} public
  using ( natlit )

{-# BUILTIN FROMNAT natlit #-}
