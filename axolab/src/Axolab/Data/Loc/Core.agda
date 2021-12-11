
module Axolab.Data.Loc.Core where

open import Axolab.Data.Nat as Nat using (ℕ; _+_)
open import Axolab.Prelude

infix  5 _≤_ _<_
infixr 6 _⋊_
infixl 6 _⋉_

-- ---------------------------------------------------------------------------------------------------------------------

record Loc : Set where
  constructor ⟨_∷_⟩
  eta-equality

  field
    row : ℕ
    col : ℕ

open Loc public

_⋉_ : Loc → ℕ → Loc
⟨ r ∷ c ⟩ ⋉ n = ⟨ r ∷ n + c ⟩

_⋊_ : ℕ → Loc → Loc
n ⋊ ⟨ r ∷ c ⟩ = ⟨ n + r ∷ c ⟩

_×_ : Loc → Loc → Loc
⟨ r₁ ∷ c₁ ⟩ × ⟨ r₂ ∷ c₂ ⟩ = ⟨ r₁ + r₂ ∷ c₁ + c₂ ⟩

-- ---------------------------------------------------------------------------------------------------------------------

data _≤_ : Loc → Loc → Set where
  row≤ : {a b : Loc} → row a Nat.< row b → a ≤ b
  col≤ : {a b : Loc} → row a ≡ row b → col a Nat.≤ col b → a ≤ b

data _<_ : Loc → Loc → Set where
  row< : {a b : Loc} → row a Nat.< row b → a < b
  col< : {a b : Loc} → row a ≡ row b → col a Nat.< col b → a < b
