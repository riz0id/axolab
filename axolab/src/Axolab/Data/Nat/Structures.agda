
module Axolab.Data.Nat.Structures where

open import Axolab.Data.Nat as Nat using (ℕ)
import Axolab.Data.Nat.Properties as Nat
open import Axolab.Prelude
open import Axolab.Relation.Structure.Proset
open import Axolab.Relation.Structure.Poset

open Proset
open Poset
open StrictPoset

-- ---------------------------------------------------------------------------------------------------------------------

ℕ/≤-Proset : Proset ℕ 0ℓ
_~_        ℕ/≤-Proset = Nat._≤_
reflexive~ ℕ/≤-Proset = Nat.reflexive≤
trans~     ℕ/≤-Proset = Nat.trans≤
isProp~    ℕ/≤-Proset = Nat.isProp≤
isSet      ℕ/≤-Proset = Nat.ℕ-isSet

ℕ/≤-Poset : Poset ℕ 0ℓ
proset   ℕ/≤-Poset = ℕ/≤-Proset
antisym≤ ℕ/≤-Poset = Nat.antisym≤

ℕ/<-StrictPoset : StrictPoset ℕ 0ℓ
_<_     ℕ/<-StrictPoset = Nat._<_
irrefl< ℕ/<-StrictPoset = Nat.irrefl<
trans<  ℕ/<-StrictPoset = Nat.trans<
isProp< ℕ/<-StrictPoset = Nat.isProp<
isSet   ℕ/<-StrictPoset = Nat.ℕ-isSet
