
open import Prelude
open import Relation.Structure.Poset

module Topos.Instances.Temporal.TemporalIndex
  {o ℓ} {T : Set o}
  (poset : DecidablePoset T ℓ)
  where

open import Categorical.Category
open import Prelude.Equality
open import Prelude.Data.Sigma
open import Prelude.Data.Product
-- open import Topos.Instances.Temporal.Interval poset
-- open import Topos.Instances.Temporal.Glue poset

open Category
open DecidablePoset poset

-- ---------------------------------------------------------------------------------------------------------------------

Interval : Set (o ⊔ ℓ)
Interval = Σ[ (t₀ , t₁) ∈ T × T ] t₀ ≤ t₁

Process : Interval → Interval → Set (o ⊔ ℓ)
Process 𝑖₂ 𝑖₁ =
  let (t¹ , tₒ¹) = fst 𝑖₁
      (t² , tₒ²) = fst 𝑖₂
   in (t¹ ≡ t²) × (tₒ¹ ≤ tₒ²)

TemporalIndex : Category (o ⊔ ℓ) (o ⊔ ℓ)
Ob     TemporalIndex = Interval
Hom    TemporalIndex = Process
id     TemporalIndex = refl , refl≤
_∘_    TemporalIndex = λ where
  (t²≡t³ , tₒ²≤tₒ³) (t¹≡t² , tₒ¹≤tₒ²) →
    (t²≡t³ ∘p t¹≡t²) , trans≤ tₒ²≤tₒ³ tₒ¹≤tₒ²
id←    TemporalIndex = ap₂ _,_ (UIP _ _) (const≤→ _)
id→    TemporalIndex = ap₂ _,_ (UIP _ _) (const≤← _)
assoc← TemporalIndex = ap₂ _,_ (UIP _ _) (assoc≤→ _ _ _)
assoc→ TemporalIndex = ap₂ _,_ (UIP _ _) (assoc≤← _ _ _)

