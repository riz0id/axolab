
module Axolab.Category.Functor.Instances.BinTree where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Data.Nat using (ℕ; suc; zero; _+_)
open import Axolab.Data.Nat.Properties using (observe<→≢)
open import Axolab.Data.Nat.Structures
open import Axolab.Relation.Negation
open import Axolab.Relation.Structure.Poset
open import Axolab.Relation.Structure.Proset
open import Axolab.Prelude

open Proset
open Poset ℕ/≤-Poset
open StrictPoset ℕ/<-StrictPoset

-- ---------------------------------------------------------------------------------------------------------------------

data BinTree {ℓ} (A : Set ℓ) : Set ℓ where
  Tip : BinTree A
  Bin : A → BinTree A → BinTree A → BinTree A

∥_∥ : ∀ {ℓ} {A : Set ℓ} → BinTree A → ℕ
∥ Tip       ∥ = 0
∥ Bin x l r ∥ = 1 + ∥ l ∥ + ∥ r ∥

record Loc : Set where
  constructor loc⟨_,_⟩
  eta-equality

  field
    row : ℕ
    col : ℕ

open Loc

data _≼_ : Loc → Loc → Set where
  row≼ : {l₁ l₂ : Loc} → row l₁ < row l₂ → l₁ ≼ l₂
  col≼ : {l₁ l₂ : Loc} → row l₁ ≡ row l₂ → col l₁ ≤ col l₂ → l₁ ≼ l₂

reflexive≼ : {l₁ l₂ : Loc} → l₁ ≡ l₂ → l₁ ≼ l₂
reflexive≼ refl = col≼ refl refl≤

trans≼ : {l₁ l₂ l₃ : Loc} → l₁ ≼ l₂ → l₂ ≼ l₃ → l₁ ≼ l₃
trans≼ (row≼ p<)    (row≼ q<)    = row≼ (trans< p< q<)
trans≼ (row≼ p<)    (col≼ q≡ q≤) = row≼ (resp</→ q≡ p<)
trans≼ (col≼ p≡ p≤) (row≼ q<)    = row≼ (resp</← (sym p≡) q<)
trans≼ (col≼ p≡ p≤) (col≼ q≡ q≤) = col≼ (p≡ ∘p q≡) (trans≤ p≤ q≤)

isProp≼ : {l₁ l₂ : Loc} (p q : l₁ ≼ l₂) → p ≡ q
isProp≼ (row≼ p<)    (row≼ q<)    = ap row≼ (isProp< p< q<)
isProp≼ (row≼ p<)    (col≼ q≡ q≤) = contradiction q≡ (observe<→≢ p<)
isProp≼ (col≼ p≡ p≤) (row≼ q<)    = contradiction p≡ (observe<→≢ q<)
isProp≼ (col≼ p≡ p≤) (col≼ q≡ q≤) = ap₂ col≼ (UIP p≡ q≡) (isProp≤ p≤ q≤)

Loc/≼-Proset : Proset Loc 0ℓ
_~_        Loc/≼-Proset = _≼_
reflexive~ Loc/≼-Proset = reflexive≼
trans~     Loc/≼-Proset = trans≼
isProp~    Loc/≼-Proset = isProp≼
