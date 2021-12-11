
module Axolab.Data.Loc.Properties where

open import Axolab.Data.Bool
open import Axolab.Data.Bot
open import Axolab.Relation.Decidable
open import Axolab.Relation.Negation
open import Axolab.Relation.Trichotomy
open import Axolab.Prelude

open import Axolab.Data.Loc.Core

private
  module Nat where
    open import Axolab.Data.Nat public
      using ( _≡?_; compare )
    open import Axolab.Data.Nat.Properties public
      using ( send<→≢; send<→≯; antisym< )
    open import Axolab.Data.Nat.Structures
    open import Axolab.Relation.Structure.Poset

    open Poset ℕ/≤-Poset public
    open StrictPoset ℕ/<-StrictPoset public

  variable
    a b c : Loc

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _≡_

Loc-isSet : (p q : a ≡ b) → p ≡ q
Loc-isSet refl refl = refl

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _≢_

row≢→loc≢ : row a ≢ row b → a ≢ b
row≢→loc≢ r₁≢r₂ a≡b = contradiction (ap row a≡b) r₁≢r₂

col≢→loc≢ : col a ≢ col b → a ≢ b
col≢→loc≢ c₁≢c₂ a≡b = contradiction (ap col a≡b) c₁≢c₂

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _≤_

reflexive≤ : a ≡ b → a ≤ b
reflexive≤ refl = col≤ refl Nat.refl≤

trans≤ : a ≤ b → b ≤ c → a ≤ c
trans≤ (row≤ p)     (row≤ q)     = row≤ (Nat.trans< p q)
trans≤ (row≤ p)     (col≤ q≡ q≤) = row≤ (Nat.resp</→ q≡ p)
trans≤ (col≤ p≡ p≤) (row≤ q)     = row≤ (Nat.resp</← (sym p≡) q)
trans≤ (col≤ p≡ p≤) (col≤ q≡ q≤) = col≤ (p≡ ∘p q≡) (Nat.trans≤ p≤ q≤)

isProp≤ : (p q : a ≤ b) → p ≡ q
isProp≤ (row≤ p)     (row≤ q)     = ap row≤ (Nat.isProp< p q)
isProp≤ (row≤ p)     (col≤ q≡ q≤) = contradiction q≡ (Nat.send<→≢ p)
isProp≤ (col≤ p≡ p≤) (row≤ q)     = contradiction p≡ (Nat.send<→≢ q)
isProp≤ (col≤ p≡ p≤) (col≤ q≡ q≤) = ap₂ col≤ (UIP p≡ q≡) (Nat.isProp≤ p≤ q≤)

-- ---------------------------------------------------------------------------------------------------------------------
-- Properties of _<_

trans< : a < b → b < c → a < c
trans< (row< p)     (row< q)     = row< (Nat.trans< p q)
trans< (row< p)     (col< q≡ q<) = row< (Nat.resp</→ q≡ p)
trans< (col< p≡ p<) (row< q)     = row< (Nat.resp</← (sym p≡) q)
trans< (col< p≡ p<) (col< q≡ q<) = col< (p≡ ∘p q≡) (Nat.trans< p< q<)

irrefl< : a ≡ b → a < b → ⊥
irrefl< a≡b (row< r<r')      = Nat.irrefl< (ap row a≡b) r<r'
irrefl< a≡b (col< refl c<c') = Nat.irrefl< (ap col a≡b) c<c'

row<→loc≢ : row a Nat.< row b → a ≢ b
row<→loc≢ r₁<r₂ a≡b = row≢→loc≢ (Nat.send<→≢ r₁<r₂) a≡b

row≮×≢→loc≮ : ¬ (row a Nat.< row b) → row a ≢ row b → ¬ (a < b)
row≮×≢→loc≮ a≮b a≢b (row< p<)    = a≮b p<
row≮×≢→loc≮ a≮b a≢b (col< p≡ q<) = contradiction p≡ a≢b

send<→≢ : a < b → a ≢ b
send<→≢ (row< p)     a≡b = contradiction (ap row a≡b) (Nat.send<→≢ p)
send<→≢ (col< p≡ p<) a≡b = contradiction (ap col a≡b) (Nat.send<→≢ p<)

send<→≮ : a < b → ¬ (b < a)
send<→≮ (row< p<)    (row< q<)    = contradiction p< (Nat.send<→≯ q<)
send<→≮ (row< p<)    (col< q≡ q<) = contradiction p< (Nat.irrefl< (sym q≡))
send<→≮ (col< p≡ p<) (row< q<)    = contradiction q< (Nat.irrefl< (sym p≡))
send<→≮ (col< p≡ p<) (col< q≡ q<) = contradiction p< (Nat.send<→≯ q<)

row≢→trichotomy : row a ≢ row b → Trichotomy (a < b) (a ≡ b) (b < a)
row≢→trichotomy {a} {b} r₁≢r₂ with Nat.compare (row a) (row b)
... | tri< r₁<r₂ _     _     = tri< (row< r₁<r₂) (row≢→loc≢ r₁≢r₂) (send<→≮ (row< r₁<r₂))
... | tri≈ _     r₁≡r₂ _     = contradiction r₁≡r₂ r₁≢r₂
... | tri> _     _     r₂<r₁ = tri> (send<→≮ (row< r₂<r₁)) (row≢→loc≢ r₁≢r₂) (row< r₂<r₁)

row≡→trichotomy : row a ≡ row b → Trichotomy (a < b) (a ≡ b) (b < a)
row≡→trichotomy {a} {b} r₁≡r₂ with Nat.compare (col a) (col b)
... | tri< c₁<c₂ c₁≢c₂ _     =
  let a<b = col< r₁≡r₂ c₁<c₂
      a≢b = col≢→loc≢ c₁≢c₂
      b≮a = send<→≮ a<b
   in tri< a<b a≢b b≮a
... | tri> _     c₁≢c₂ c₂<c₁ =
  let b<a = col< (sym r₁≡r₂) c₂<c₁
      a≢b = col≢→loc≢ c₁≢c₂
      a≮b = send<→≮ b<a
   in tri> a≮b a≢b b<a
... | tri≈ _ c₁≡c₂ _ rewrite →rewrite (ap₂ ⟨_∷_⟩ r₁≡r₂ c₁≡c₂) =
  tri≈ (irrefl< refl) refl (irrefl< refl)

trichotomous< : (a b : Loc) → Trichotomy (a < b) (a ≡ b) (b < a)
trichotomous< ⟨ r₁ ∷ c₁ ⟩ ⟨ r₂ ∷ c₂ ⟩ with r₁ Nat.≡? r₂
... | because ._ (of-no  r₁≢r₂) = row≢→trichotomy r₁≢r₂
... | because ._ (of-yes r₁≡r₂) = row≡→trichotomy r₁≡r₂

isProp< : (p q : a < b) → p ≡ q
isProp< (row< p)     (row< q)     = ap row< (Nat.isProp< p q)
isProp< (row< p)     (col< q≡ q<) = contradiction q≡ (Nat.send<→≢ p)
isProp< (col< p≡ p<) (row< q)     = contradiction p≡ (Nat.send<→≢ q)
isProp< (col< p≡ p<) (col< q≡ q<) = ap₂ col< (UIP p≡ q≡) (Nat.isProp< p< q<)
