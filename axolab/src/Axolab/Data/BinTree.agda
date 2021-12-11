
module Axolab.Data.BinTree where

open import Axolab.Data.Bot
open import Axolab.Data.Nat as Nat
open import Axolab.Data.Product
open import Axolab.Data.Top
open import Axolab.Relation.Decidable hiding (map)
open import Axolab.Prelude
open import Axolab.Prelude.Function

open import Axolab.Data.BinTree.Core public
open import Axolab.Data.BinTree.Properties

open Homomorphism

private
  variable
    ℓ : Level
    A : Set ℓ

-- --------------------------------------------------------------------------------------------------------------------

IdHomo : {X : Tree A} → Homomorphism X X
ϕ           IdHomo = idf
homomorphic IdHomo = map-id _

_∘H_ : {X Y Z : Tree A} → Homomorphism Y Z → Homomorphism X Y → Homomorphism X Z
_∘H_ g f .ϕ           = Homomorphism.ϕ g ∘ Homomorphism.ϕ f
_∘H_ g f .homomorphic = sym (map-∘ f.ϕ g.ϕ) ∘p ap (map g.ϕ) f.homomorphic ∘p g.homomorphic
  where
    module f = Homomorphism f
    module g = Homomorphism g

Homomorphism≡ : {X Y : Tree A} {f g : Homomorphism X Y} → Homomorphism.ϕ f ≡ Homomorphism.ϕ g → f ≡ g
Homomorphism≡ {f = homomorphism _ p}
              {g = homomorphism _ q}
              refl
  rewrite →rewrite (UIP p q) = refl

-- --------------------------------------------------------------------------------------------------------------------

insert : A → Tree A → Tree A
insert x Tip           = Bin Tip x Tip
insert x (Bin T₁ y T₂) = {!!}

-- rotate← : Tree A → Tree A
-- rotate← Tip                      = Tip
-- rotate← (Bin T₁ x Tip)           = Bin T₁ x Tip
-- rotate← (Bin T₁ x (Bin T₂ y T₃)) = Bin (Bin T₁ x T₂) y T₃

-- balance : Tree A → Tree A
-- balance Tip                                 = Tip
-- balance (Bin Tip           x Tip)           = Bin Tip x Tip
-- balance (Bin (Bin T₁ x T₂) y Tip)           = Bin (Bin T₁ x T₂) y Tip
-- balance (Bin Tip           x (Bin T₁ y T₂)) = Bin Tip x (Bin T₁ y T₂)
-- balance (Bin (Bin T₁ x T₂) y (Bin T₃ z T₄)) = {!!}
