
module Axolab.Relation.Decidable where

open import Axolab.Data.Bool.Core
open import Axolab.Data.Bot
open import Axolab.Prelude
open import Axolab.Prelude.Function
open import Axolab.Relation.Negation

private
  variable
    ℓ ℓ' : Level

-- ---------------------------------------------------------------------------------------------------------------------

data Reflects (P : Set ℓ) : Bool → Set ℓ where
  of-yes : P       → Reflects P true
  of-no  : (P → ⊥) → Reflects P false

record Dec (P : Set ℓ) : Set ℓ where
  constructor because
  eta-equality

  field
    does    : Bool
    witness : Reflects P does

open Dec public

Decidable : {A : Set ℓ} {B : Set ℓ'} → ((x : A) → (y : B) → Set (ℓ ⊔ ℓ')) → Set (ℓ ⊔ ℓ')
Decidable _~_ = ∀ x y → Dec (x ~ y)

map : {P : Set ℓ} {Q : Set ℓ'} → (P → Q) → (Q → P) → Dec P → Dec Q
map from to p?                         .does    = does p?
map from to (because false (of-no ¬p)) .witness = of-no  (¬p ∘ to)
map from to (because true  (of-yes p)) .witness = of-yes (from p)
