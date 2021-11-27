
module Axolab.Data.Nat.Core where

open import Axolab.Prelude

open import Agda.Builtin.Nat public
  using    ( suc; zero
           ; _+_ )
  renaming ( Nat to ℕ
           ; _-_ to _∸_
           ; _==_ to _≡ᵇ_; _<_ to _<ᵇ_ )

-- ---------------------------------------------------------------------------------------------------------------------
