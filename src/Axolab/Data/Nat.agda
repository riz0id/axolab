
module Axolab.Data.Nat where

open import Axolab.Algebra.Theory
open import Axolab.Data.Vect
open import Axolab.Prelude.Primitive.Nat public
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

ℕ[+]⊨monoid : ℕ ⊨ monoid
ℕ[+]⊨monoid = mon where
  open Interpretation
  open Signature
  open Theory

  +id→ : (n : ℕ) → n ≡ n + 0
  +id→ zero    = refl
  +id→ (suc n) = ap suc (+id→ n)

  +assoc← : (m n o : ℕ) → m + (n + o) ≡ m + n + o
  +assoc← zero    n o = refl
  +assoc← (suc m) n o = ap suc (+assoc← m n o)

  mon : ℕ ⊨ monoid
  interp mon unit nil           = 0
  interp mon ⨂    (m ∷ n ∷ nil) = m + n
  sound  mon associativity  (m ∷ n ∷ o ∷ nil) = +assoc← m n o
  sound  mon left-identity  (n ∷ nil) = refl
  sound  mon right-identity (n ∷ nil) = +id→ n
