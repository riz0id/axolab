
module Axolab.Prelude.Function where

open import Axolab.Prelude

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

infixr 5 _∘_

-- ---------------------------------------------------------------------------------------------------------------------

idf : A → A
idf x = x

_∘_ : (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
