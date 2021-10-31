
open import Categorical.Category

module Categorical.Category.Structure.Cocartesian {o ℓ} (C : Category o ℓ) where

open import Categorical.Bifunctor
open import Categorical.Functor
open import Categorical.Object.Coproduct C
open import Categorical.Object.Initial C
open import Prelude
open import Prelude.Equality
open import Prelude.Data.Product using (_,_; fst; snd)

open Category C
open Functor

private
  variable
    A B X Y Z W : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Cocartesian : Setoid (o ⊔ ℓ) where
  infixr 5 _+₀_ _+₁_

  field
    coproduct : A ∐ B
    initial   : Initial

  open module initial = Initial initial public
    using    ( ⊥ )
    renaming ( ! to id₀; !-unique to +-unique; !-unique₂ to +-unique₂ )

  _+₀_ : Ob → Ob → Ob
  A +₀ B = Coproduct.A+B coproduct

  _+₁_ : Hom A X → Hom B X → Hom (A +₀ B) X
  f +₁ g = Coproduct.[_,_] coproduct f g

  inj₁ : Hom A (A +₀ B)
  inj₁ = Coproduct.inj₁ coproduct

  inj₂ : Hom B (A +₀ B)
  inj₂ = Coproduct.inj₂ coproduct

  open PropReasoning

  -- inj₁+inj₂≡id : inj₁ +₁ inj₂ ≡ id {A +₀ B}
  -- inj₁+inj₂≡id = sym {!+-unique!}

  -- TODO!
  postulate -+- : Bifunctor C C C
  -- F₀   -+- (A , B) = A +₀ B
  -- F₁   -+- (f , g) = inj₁ ∘ f +₁ inj₂ ∘ g
  -- F-id -+- =
  --   inj₁ ∘ id +₁ inj₂ ∘ id ≡⟨ ap₂ _+₁_ id→ id→ ⟩
  --   inj₁ +₁ inj₂           ≡⟨ {!!} ⟩
  --   id                     ∎
  -- F-∘  -+- = {!!}

  _+- : (A : Ob) → Endofunctor C
  A +- = Left -+- A

  -+_ : (A : Ob) → Endofunctor C
  -+ A = Right -+- A
