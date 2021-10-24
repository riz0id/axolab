
module Prelude.Reflection.Arg where

open import Prelude.Data.String
open import Agda.Builtin.Reflection public
  using    ( Arg; arg
           ; ArgInfo; arg-info
           ; Modality; modality
           ; Quantity; quantity-0; quantity-ω
           ; Visibility; visible; hidden
           ; Relevance; relevant; irrelevant )
  renaming ( instance′ to instance' )
open import Prelude.Primitive

private
  variable
    ℓ : Level
    A : Setoid ℓ

-- ---------------------------------------------------------------------------------------------------------------------
-- Argument Patterns

-- Relevant-ω arguments
pattern rel-vω = arg-info visible   (modality relevant quantity-ω)
pattern rel-hω = arg-info hidden    (modality relevant quantity-ω)
pattern rel-iω = arg-info instance' (modality relevant quantity-ω)

-- Irrelevant-ω arguments
pattern irr-vω = arg-info visible   (modality irrelevant quantity-ω)
pattern irr-hω = arg-info hidden    (modality irrelevant quantity-ω)
pattern irr-iω = arg-info instance' (modality irrelevant quantity-ω)

-- Relevant-0 arguments
pattern rel-v0 = arg-info visible   (modality relevant quantity-0)
pattern rel-h0 = arg-info hidden    (modality relevant quantity-0)
pattern rel-i0 = arg-info instance' (modality relevant quantity-0)

-- Irrelevant-0 arguments
pattern irr-v0 = arg-info visible   (modality irrelevant quantity-0)
pattern irr-h0 = arg-info hidden    (modality irrelevant quantity-0)
pattern irr-i0 = arg-info instance' (modality irrelevant quantity-0)

-- ---------------------------------------------------------------------------------------------------------------------
-- Show/Display functions on arguments

showVisibility : Visibility → String
showVisibility visible   = "visible"
showVisibility hidden    = "hidden"
showVisibility instance' = "instance'"

showRelevance : Relevance → String
showRelevance relevant   = "relevant"
showRelevance irrelevant = "irrelevant"

showQuantity : Quantity → String
showQuantity quantity-0 = "quantity-0"
showQuantity quantity-ω = "quantity-ω"

showModality : Modality → String
showModality (modality relevant   quantity-0) = "relevant-0"
showModality (modality relevant   quantity-ω) = "relevant-ω"
showModality (modality irrelevant quantity-0) = "irrelevant-0"
showModality (modality irrelevant quantity-ω) = "irrelevant-ω"

showArgInfo : ArgInfo → String
showArgInfo (arg-info v m) = "arg-info " ++ showVisibility v ++ showModality m

showArg : Arg A → String
showArg (arg (arg-info v m) _) = "arg " ++ showVisibility v ++ showModality m
