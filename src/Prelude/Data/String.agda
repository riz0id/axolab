
module Prelude.Data.String where

import Agda.Builtin.String as String
open String public
  using    ( String )
  renaming ( primStringUncons   to uncons
           ; primStringToList   to toList
           ; primStringFromList to fromList
           ; primShowString     to show )

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _++_

_++_ : String → String → String
_++_ = String.primStringAppend
