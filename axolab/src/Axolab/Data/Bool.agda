
module Axolab.Data.Bool where

open import Axolab.Prelude
open import Axolab.Data.Bot
open import Axolab.Data.Top
open import Axolab.Relation.Decidable

open import Axolab.Data.Bool.Core public

-- ---------------------------------------------------------------------------------------------------------------------

T : Bool → Set
T false = ⊥
T true  = ⊤

T? : (b : Bool) → Dec (T b)
T? b     .does    = b
T? false .witness = of-no  λ ()
T? true  .witness = of-yes tt

F : Bool → Set
F false = ⊤
F true  = ⊥
