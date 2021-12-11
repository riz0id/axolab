-- Weighted Binary Trees.
--
-- WTree is a binary tree balanced by a total ordering.
--

open import Axolab.Relation.Structure.Toset

module Axolab.Data.WTree
  {o ℓ} {A : Set o}
  (strictToset : StrictToset A ℓ)
  where

open import Axolab.Data.Bot
open import Axolab.Data.Product
open import Axolab.Data.Top
open import Axolab.Relation.Trichotomy

open module strictToset = StrictToset strictToset

infix 5 _≼⁺_ _≼⁻_

-- --------------------------------------------------------------------------------------------------------------------

mutual
  record Branch : Set o where
    inductive
    constructor branch
    eta-equality

    field
      root     : A
      subtree← : Σ[ T ∈ WTree ] T ≼⁻ root
      subtree→ : Σ[ T ∈ WTree ] root ≼⁺ T

  data WTree : Set o where
    tip : WTree
    bin : Branch → WTree

  _≼⁺_ : A → WTree → Set
  x ≼⁺ tip    = ⊤
  x ≼⁺ bin B with compare x (Branch.root B)
  ... | tri< _ _ _ = ⊥
  ... | tri≈ _ _ _ = ⊤
  ... | tri> _ _ _ = ⊤

  _≼⁻_ : WTree → A → Set {!!}
  tip   ≼⁻ x = ⊤
  bin B ≼⁻ x with compare (Branch.root B) x
  ... | tri< _ _ _ = ⊤
  ... | tri≈ _ _ _ = ⊤
  ... | tri> _ _ p = ⊥

open Branch public
