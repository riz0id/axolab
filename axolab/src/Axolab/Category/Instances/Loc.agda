-- Loc is the thin category of source locations.
--

module Axolab.Category.Instances.Loc where

open import Axolab.Category
open import Axolab.Category.Constructions.Thin
open import Axolab.Prelude

import Axolab.Data.Loc.Structures as Loc

-- ---------------------------------------------------------------------------------------------------------------------

Loc : Category 0ℓ 0ℓ
Loc = Thin Loc.Loc/≤-Proset
