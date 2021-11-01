
module Axolab.Prelude.Primitive.Nat where

open import Agda.Builtin.Nat public
  using    ( Nat; zero; suc
           ; _+_; _*_ )
  renaming ( _-_ to _∸_; _==_ to _≡?_; _<_ to _<?_ )

-- ---------------------------------------------------------------------------------------------------------------------
