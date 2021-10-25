module Categorical.NaturalTransformation where

open import Categorical.Category
open import Categorical.Functor
open import Categorical.NaturalTransformation.NaturalIsomorphism
open import Categorical.NaturalTransformation.Core public
open import Prelude
open import Prelude.Equality

open NaturalTransformation

private
  variable
    o ℓ o' ℓ' : Level
    C : Category o ℓ
    D : Category o' ℓ'

-- ---------------------------------------------------------------------------------------------------------------------

-- Invoke UIP to assert that natural transformations are equivalence when their assignment maps are component-wise
-- equivalent.
NT≡ : {C : Category o ℓ} {D : Category o' ℓ'} {F G : Functor C D} {α β : F ⇒ G} → η α ≡ η β → α ≡ β
NT≡ refl = ap (λ e → record { η = _; natural = e }) inside where
  inside = funExt λ _ → funExt λ _ → funExt λ _ → UIP _ _

id-η← : {F G : Functor C D} {α : F ⇒ G} → idNT ∘⇑ α ≡ α
id-η← {D = D} = NT≡ (funExt λ _ → D.id←) where
     module D = Category D

id-η→ : {F G : Functor C D} {α : F ⇒ G} → α ∘⇑ idNT ≡ α
id-η→ {D = D} = NT≡ (funExt λ _ → D.id→) where
     module D = Category D

module _ {F G H I : Functor C D} {α : F ⇒ G} {β : G ⇒ H} {γ : H ⇒ I} where
  private module D = Category D

  assoc-η→ : (γ ∘⇑ β) ∘⇑ α ≡ γ ∘⇑ (β ∘⇑ α)
  assoc-η→ = NT≡ (funExt λ _ → D.assoc→)

  assoc-η← : γ ∘⇑ (β ∘⇑ α) ≡ (γ ∘⇑ β) ∘⇑ α
  assoc-η← = NT≡ (funExt λ _ → D.assoc←)
