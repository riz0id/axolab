
open import Axolab.Prelude

module Axolab.Relation.Structure.Proset {o} (A : Set o) where

private
  variable
    x y z w : A

-- ---------------------------------------------------------------------------------------------------------------------

record Proset (ℓ : Level) : Set (o ⊔ lsuc ℓ) where
  eta-equality
  infix 6 _~_

  field
    _~_        : A → A → Set ℓ
    reflexive~ : x ≡ y → x ~ y
    trans~     : x ~ y → y ~ z → x ~ z

  field
    -- UIP coherence
    isSet : (p q : x ≡ y) → p ≡ q
    isProp~ : (p q : x ~ y) → p ≡ q

  refl~ : {x : A} → x ~ x
  refl~ = reflexive~ refl

  resp~/← : {x' : A} → x ~ y → x ≡ x' → x' ~ y
  resp~/← x≤y x~x' = trans~ (reflexive~ (sym x~x')) x≤y

  resp~/→ : {y' : A} → x ~ y → y ≡ y' → x ~ y'
  resp~/→ x≤y y~y' = trans~ x≤y (reflexive~ y~y')

  id~/← : (x~y : x ~ y) → trans~ x~y refl~ ≡ x~y
  id~/← x~y = isProp~ (trans~ x~y refl~) x~y

  id~/→ : (x~y : x ~ y) → trans~ refl~ x~y ≡ x~y
  id~/→ x~y = isProp~ (trans~ refl~ x~y) x~y

  assoc~/← : (x~y : x ~ y) (y~z : y ~ z) (z~w : z ~ w) → trans~ x~y (trans~ y~z z~w) ≡ trans~ (trans~ x~y y~z) z~w
  assoc~/← x~y y~z z~w = isProp~ (trans~ x~y (trans~ y~z z~w)) (trans~ (trans~ x~y y~z) z~w)

  assoc~/→ : (x~y : x ~ y) (y~z : y ~ z) (z~w : z ~ w) → trans~ (trans~ x~y y~z) z~w ≡ trans~ x~y (trans~ y~z z~w)
  assoc~/→ x~y y~z z~w = isProp~ (trans~ (trans~ x~y y~z) z~w) (trans~ x~y (trans~ y~z z~w))
