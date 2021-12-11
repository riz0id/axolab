-- Binary Trees of Bounded Balance.
--

module Axolab.Data.BinTree.Core where

open import Axolab.Relation.Decidable hiding (map)
open import Axolab.Data.Bool
open import Axolab.Data.Bot
open import Axolab.Data.Nat
open import Axolab.Data.Product
open import Axolab.Data.Top
open import Axolab.Relation.Trichotomy
open import Axolab.Prelude hiding (_⊔_)

private
  variable
    ℓ : Level
    A : Set ℓ

-- ---------------------------------------------------------------------------------------------------------------------

data Tree {ℓ} (A : Set ℓ) : Set ℓ where
  Tip : Tree A
  Bin : Tree A → A → Tree A → Tree A

NonEmpty? : Tree A → Set
NonEmpty? Tip         = ⊥
NonEmpty? (Bin _ _ _) = ⊤

map : (A → A) → Tree A → Tree A
map ϕ Tip         = Tip
map ϕ (Bin l x r) = Bin (map ϕ l) (ϕ x) (map ϕ r)

-- Cardinality/size of a tree.
∥_∥ : Tree A → ℕ
∥ Tip         ∥ = 0
∥ Bin T₁ x T₂ ∥ = 1 + ∥ T₁ ∥ + ∥ T₂ ∥

-- Maximum number of subtrees.
height : Tree A → ℕ
height Tip           = 0
height (Bin T₁ _ T₂) = 1 + (height T₁ ⊔ height T₂)

-- ---------------------------------------------------------------------------------------------------------------------

record Homomorphism {ℓ} {U : Set ℓ} (X Y : Tree U) : Set (lsuc ℓ) where
  constructor homomorphism
  eta-equality

  field
    ϕ           : U → U
    homomorphic : map ϕ X ≡ Y
