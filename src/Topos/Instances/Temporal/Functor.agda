
open import Axolab.Category
open import Axolab.Prelude

postulate DecidablePoset : ∀ {ℓ} (A : Set ℓ) (ℓ' : Level) → Set

module Topos.Instances.Temporal.Functor
  {o₁ ℓ₁ o₂ ℓ₂} {T : Setoid o₁}
  (T-poset : DecidablePoset T ℓ₁)
  (C       : Category o₂ ℓ₂)
  where

open import Categorical.Category.Instances.Functors
open import Categorical.Category.Instances.Product renaming (_×Cat_ to _×_)
open import Categorical.Category.Bundle.CartesianClosed
open import Categorical.Functor
open import Topos.Instances.Temporal.TemporalIndex (DecidablePoset.poset T-poset)
open import Topos.Instances.Temporal.Time T-poset
open import Topos.Instances.Temporal.Interval (DecidablePoset.poset T-poset)
open import Topos.Instances.Temporal.ISet (DecidablePoset.poset T-poset)
open import Prelude.Data.Product using (_,_)
open import Prelude.Equality
open import Relation.Decidable

open Category
open Functor
open DecidablePoset Time∞DecidablePoset

-- ---------------------------------------------------------------------------------------------------------------------

-- Cᴵ : Category (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂)
-- Cᴵ = Functors TemporalIndex C

-- module _ (𝑖 : Interval) where
--   private module 𝑖 = Interval 𝑖

--   ∐⟨-]-syntax : {t : T} → t ∈⟨ 𝑖 ] → Functor TemporalIndex C
--   ∐⟨-]-syntax {t} (𝑖ₜ≤t , iₜ≢t , t≤𝑖ₒ) =
--     record
--       { F₀   = λ 𝑖₂ → {!!}
--       ; F₁   = {!!}
--       ; F-id = {!!}
--       ; F-∘  = {!!}
--       }

--   S : Time∞ → ISet → ISet → ISet
--   S = {!!}

--   ▷₀'' : Ob (Time∞Cat × Cᴵ × Cᴵ) → Interval → Ob Cᴵ
--   ▷₀'' (time tb , A , B) 𝑖 = {!!}
--   ▷₀'' (inf     , A , B) 𝑖 = {!!}
--   -- with (compare≤ (time 𝑖.ₜ) tb , compare≤ tb (time 𝑖.ₒ))
--   -- ... | no  t≤tb , yes tb≤tₒ = contradiction {!!} t≤tb
--   -- ... | no  t≤tb , no  tb≤tₒ = {!!}
--   -- ... | yes t≤tb , yes tb≤tₒ = {!!}
--   -- ... | _        , no  tb≤tₒ = {!!}

--   ▷'' : Functor (Time∞Cat × Cᴵ × Cᴵ) Cᴵ
--   F₀   ▷'' = {!!}
--   F₁   ▷'' = {!!}
--   F-id ▷'' = {!!}
--   F-∘  ▷'' = {!!}
