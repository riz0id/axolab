

module Topos.Instances.Temporal.CPC where

open import Categorical.Category
open import Categorical.Category.Instances.CCCC
open import Categorical.Category.Instances.Functors
open import Categorical.Category.Instances.Product
  renaming ( _×Cat_ to _×_ )
open import Categorical.Category.Instances.Thin
open import Categorical.Functor
open import Prelude
open import Prelude.Equality
open import Prelude.Data.Product
  using ( _,_ )
open import Prelude.Data.Sigma
  using ( _,_ )
open import Relation.Decidable
open import Relation.Structure.Poset

open import Topos.Instances.Temporal.TemporalIndex
open import Topos.Instances.Temporal.Time

open Category
open Functor

-- ---------------------------------------------------------------------------------------------------------------------

record CPC {o ℓ} (Time : Set o) (M : Category o ℓ) : Set (lsuc (o ⊔ ℓ)) where
  field
    MCCCC : CCCC M
    poset : DecidablePoset Time ℓ

  module M     = Category M
  module poset = DecidablePoset poset

  Ix : Category (o ⊔ ℓ) (o ⊔ ℓ)
  Ix = TemporalIndex poset

  W∞ : Category o ℓ
  W∞ = Thin (Time∞Poset poset)

  Proc : Category (o ⊔ ℓ) (o ⊔ ℓ)
  Proc = Functors Ix M

  field
    Cocone

  private
    open DecidablePoset poset
      using    ( compare≤ )

    open DecidablePoset (Time∞DecidablePoset poset)
      using    ( )
      renaming ( compare≤ to compare≤∞ )

    open CCCC MCCCC

    ∐⟨_,_] : Time → Time → (Time → M.Ob) → M.Ob
    ∐⟨ t , t* ] f
      with compare≤ t t*
    ... | yes t≤t* = f t +₀ {!!} -- no way to recur on the successor of t...
    ... | no  t*≤t = {!!} -- needs total order, should be < although it might not make a difference

    S₀ : Functor Ix M → Functor Ix M → Time → Time → Time → M.Ob
    S₀ A B t* t tₒ = {!!}

    ▷₀'' : Ob (W∞ × Proc × Proc) → Ob Proc
    F₀   (▷₀'' (tb , A , B)) ((t , tₒ) , t≤tₒ)
      with compare≤∞ tb (time t)
    ... | yes tb≤t  = {!!}
    ... | no  t≤tb
      with compare≤∞ tb (time tₒ)
    ... | yes tb≤tₒ = {!!}
    ... | no  tₒ≤tb = {!!} +₀ {!!}
    F₁   (▷₀'' 𝑖) = {!!}
    F-id (▷₀'' 𝑖) = {!!}
    F-∘  (▷₀'' 𝑖) = {!!}

  ▷'' : Functor (W∞ × Proc × Proc) Proc
  ▷'' =
    record
      { F₀   = {!!}
      ; F₁   = {!!}
      ; F-id = {!!}
      ; F-∘  = {!!}
      }
    where
      ▷''₀ : Ob (W∞ × Proc × Proc) → Ob Proc
      ▷''₀ (tb , A , B)  =
        record
          { F₀   = λ 𝑖 → {!!}
          ; F₁   = {!!}
          ; F-id = {!!}
          ; F-∘  = {!!}
          }


  -- open module Proc = Category Proc

  -- field
  --   cartesian  : Cartesian Proc
  --   closed     : CartesianClosed Proc cartesian
  --   coproducts : (A B : Ob) → Coproduct Proc A B

  -- _+₀_ : Ob → Ob → Ob
  -- A +₀ B = Coproduct.A+B (coproducts A B)

  -- _+₁_ : {A B X : Ob} → Hom A X → Hom B X → Hom (A +₀ B) X
  -- f +₁ g = Coproduct.[_,_] (coproducts _ _) f g

-- CPC : ∀ {o ℓ} {T : Set o} → DecidablePoset T ℓ → CCCC o ℓ → Category (o ⊔ ℓ) (o ⊔ ℓ)
-- CPC T B = Functors (TemporalIndex T) (CCCC.U B)

-- module _ {o ℓ} {T : Set o} (decPoset : DecidablePoset T ℓ) where
--   open module decPoset = DecidablePoset decPoset

--   Ix : Category (o ⊔ ℓ) (o ⊔ ℓ)
--   Ix = TemporalIndex poset

--   W∞ : Category o ℓ
--   W∞ = Thin (Time∞Poset decPoset)

--   record CCCC : Set (o ⊔ ℓ) where
--     field
--       C
--     field
--       cartesian  : (𝑖 : Ob Ix) → Cartesian (C 𝑖)
--       closed     : (𝑖 : Ob Ix) → CartesianClosed (C 𝑖) (cartesian 𝑖)
--       coproducts : (𝑖 : Ob Ix) (A B : Ob (C 𝑖)) → Coproduct (C 𝑖) A B

--   ▷''
