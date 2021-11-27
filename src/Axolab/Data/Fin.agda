
module Axolab.Data.Fin where

open import Axolab.Data.Nat
open import Axolab.Data.Fin.Core public
open import Axolab.Prelude

infix 10 #_

-- ---------------------------------------------------------------------------------------------------------------------

#_ : ∀ {n} (m : ℕ) → {{suc m ∸ n ≡ 0}} → Fin n
#_ {zero}  m {{}}
#_ {suc n} zero    = fzero
#_ {suc n} (suc m) = fsuc (# m)
