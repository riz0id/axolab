
module Axolab.Category.Instances.Interval where

open import Axolab.Category
open import Axolab.Data.Bool
open import Axolab.Data.Bot
open import Axolab.Data.Top
open import Axolab.Prelude

open Category

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _ðâ_

data _ðâ_ : Bool â Bool â Set where
  IâI : â {e} â e ðâ e
  ðâð : false ðâ true

Interval : Category 0â 0â
Interval = cat where
  _ðâ_ : {X Y Z : Bool} â Y ðâ Z â X ðâ Y â X ðâ Z
  _ðâ_ IâI IâI = IâI
  _ðâ_ IâI ðâð = ðâð
  _ðâ_ ðâð IâI = ðâð

  ðâ id : {X Y : Bool} (f : X ðâ Y) â IâI ðâ f â¡ f
  ðâ id IâI = refl
  ðâ id ðâð = refl

  ðâid : {X Y : Bool} (f : X ðâ Y) â f ðâ IâI â¡ f
  ðâid IâI = refl
  ðâid ðâð = refl

  ðâ assoc : â {X Y Z W} (f : X ðâ Y) (g : Y ðâ Z) (h : Z ðâ W) â (h ðâ (g ðâ f)) â¡ ((h ðâ g) ðâ f)
  ðâ assoc IâI IâI IâI = refl
  ðâ assoc ðâð IâI IâI = refl
  ðâ assoc IâI IâI ðâð = refl
  ðâ assoc IâI ðâð IâI = refl

  ðâassoc : â {X Y Z W} (f : X ðâ Y) (g : Y ðâ Z) (h : Z ðâ W) â ((h ðâ g) ðâ f) â¡ (h ðâ (g ðâ f))
  ðâassoc IâI IâI IâI = refl
  ðâassoc ðâð IâI IâI = refl
  ðâassoc IâI IâI ðâð = refl
  ðâassoc IâI ðâð IâI = refl

  cat : Category 0â 0â
  Ob     cat = Bool
  Hom    cat = _ðâ_
  id     cat = IâI
  _â_    cat = _ðâ_
  idâ    cat = ðâ id _
  idâ    cat = ðâid _
  assocâ cat = ðâ assoc _ _ _
  assocâ cat = ðâassoc _ _ _
