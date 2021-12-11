
module Axolab.Data.Loc.Structures where

-- open import Axolab.Data.Nat as Nat using (ℕ; _+_)
open import Axolab.Data.Loc.Core as Loc using (Loc)
import Axolab.Data.Loc.Properties as Loc
open import Axolab.Relation.Structure.Poset
open import Axolab.Relation.Structure.Proset
open import Axolab.Relation.Structure.Toset
open import Axolab.Prelude

open Poset
open StrictPoset
open Proset
open StrictToset

-- ---------------------------------------------------------------------------------------------------------------------
-- Structures of _≤_

Loc/≤-Proset : Proset Loc 0ℓ
_~_        Loc/≤-Proset = Loc._≤_
reflexive~ Loc/≤-Proset = Loc.reflexive≤
trans~     Loc/≤-Proset = Loc.trans≤
isProp~    Loc/≤-Proset = Loc.isProp≤
isSet      Loc/≤-Proset = Loc.Loc-isSet

-- ---------------------------------------------------------------------------------------------------------------------
-- Structures of _<_

Loc/<-StrictPoset : StrictPoset Loc 0ℓ
_<_     Loc/<-StrictPoset = Loc._<_
irrefl< Loc/<-StrictPoset = Loc.irrefl<
trans<  Loc/<-StrictPoset = Loc.trans<
isProp< Loc/<-StrictPoset = Loc.isProp<
isSet   Loc/<-StrictPoset = Loc.Loc-isSet

Loc<-StrictToset : StrictToset Loc 0ℓ
_<_     Loc<-StrictToset = Loc._<_
trans<  Loc<-StrictToset = Loc.trans<
compare Loc<-StrictToset = Loc.trichotomous<
isSet   Loc<-StrictToset = Loc.Loc-isSet
isProp< Loc<-StrictToset = Loc.isProp<
