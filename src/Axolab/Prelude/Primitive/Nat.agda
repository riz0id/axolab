
module Axolab.Prelude.Primitive.Nat where

open import Agda.Builtin.Nat public
  using    ( zero; suc
           ; _+_; _*_ )
  renaming ( Nat to ℕ; _-_ to _∸_; _==_ to _≡?_; _<_ to _<?_ )

-- ---------------------------------------------------------------------------------------------------------------------
