
module Axolab.Relation.Negation where

open import Axolab.Data.Bot
open import Axolab.Prelude

infix 3 ¬_
infix 4 _≢_

-- ---------------------------------------------------------------------------------------------------------------------

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬_ A = A → ⊥

_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≢ y = ¬ (x ≡ y)

contradiction : ∀ {ℓ ℓ'} {A : Set ℓ} {X : Set ℓ'} → A → ¬ A → X
contradiction p ¬p = absurd (¬p p)
