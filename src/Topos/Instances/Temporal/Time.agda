open import Prelude
open import Relation.Structure.Poset

module Topos.Instances.Temporal.Time
  {o ℓ} {T : Set o}
  (T-poset : DecidablePoset T ℓ)
  where

open import Relation.Decidable
open import Relation.Structure.Proset
open import Prelude.Data.Bool
open import Prelude.Equality

private
  module T-poset = DecidablePoset T-poset
    renaming ( _≤_        to _≼_
             ; reflexive≤ to reflexive≼
             ; trans≤     to trans≼
             ; antisym≤   to antisym≼
             ; prop≤      to prop≼
             ; compare≤   to compare≼ )

open T-poset
open Poset
open DecidablePoset
open Proset

-- ---------------------------------------------------------------------------------------------------------------------

infix 4 _≤∞_

data Time∞ : Set o where
  time : T → Time∞
  inf  : Time∞

data _≤∞_ : Time∞ → Time∞ → Set ℓ where
  inj≤ : {t₁ t₂ : T} → t₁ ≼ t₂ → time t₁ ≤∞ time t₂
  inj∞ : {t₁ : Time∞} → t₁ ≤∞ inf

reflexive≤∞ : {t₁ t₂ : Time∞} → t₁ ≡ t₂ → t₁ ≤∞ t₂
reflexive≤∞ {time t₂} refl = inj≤ (reflexive≼ refl)
reflexive≤∞ {inf}     refl = inj∞

trans≤∞ : {t₁ t₂ t₃ : Time∞} → t₁ ≤∞ t₂ → t₂ ≤∞ t₃ → t₁ ≤∞ t₃
trans≤∞ (inj≤ p) (inj≤ q) = inj≤ (trans≼ p q)
trans≤∞ (inj≤ p) inj∞      = inj∞
trans≤∞ inj∞     inj∞      = inj∞

prop≤∞ : {t₁ t₂ : Time∞} (p q : t₁ ≤∞ t₂) → p ≡ q
prop≤∞ (inj≤ p) (inj≤ q) = ap inj≤ (prop≼ p q)
prop≤∞ inj∞     inj∞     = refl

antisym≤∞ : {t₁ t₂ : Time∞} → t₁ ≤∞ t₂ → t₂ ≤∞ t₁ → t₁ ≡ t₂
antisym≤∞ (inj≤ p) (inj≤ q) = ap time (antisym≼ p q)
antisym≤∞ inj∞     inj∞     = refl

reflects≼⇒reflects≤∞ : {t₁ t₂ : T} {p : Bool} → Reflects (t₁ ≼ t₂) p → Reflects (time t₁ ≤∞ time t₂) p
reflects≼⇒reflects≤∞ (reflYes p)  = reflYes (inj≤ p)
reflects≼⇒reflects≤∞ (reflNo  ¬p) = reflNo  λ where (inj≤ p) → contradiction p ¬p

decidable≤∞ : Decidable o ℓ _≤∞_
does    (decidable≤∞ (time t₁) (time t₂)) = does (compare≼ t₁ t₂)
does    (decidable≤∞ (time t₁) inf)       = true
does    (decidable≤∞ inf       (time t₂)) = false
does    (decidable≤∞ inf       inf)       = true
witness (decidable≤∞ (time t₁) (time t₂)) = reflects≼⇒reflects≤∞ (witness (compare≼ t₁ t₂))
witness (decidable≤∞ (time t₁) inf)       = reflYes inj∞
witness (decidable≤∞ inf       (time t₁)) = reflNo (λ ())
witness (decidable≤∞ inf       inf)       = reflYes (reflexive≤∞ refl)

Time∞Proset : Proset Time∞ ℓ
_≤_        Time∞Proset = _≤∞_
reflexive≤ Time∞Proset = reflexive≤∞
trans≤     Time∞Proset = trans≤∞
prop≤      Time∞Proset = prop≤∞

Time∞Poset : Poset Time∞ ℓ
proset   Time∞Poset = Time∞Proset
antisym≤ Time∞Poset = antisym≤∞

Time∞DecidablePoset : DecidablePoset Time∞ ℓ
poset      Time∞DecidablePoset = Time∞Poset
decidable≤ Time∞DecidablePoset = decidable≤∞
