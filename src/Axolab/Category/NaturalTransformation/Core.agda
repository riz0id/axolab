
module Axolab.Category.NaturalTransformation.Core where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o ℓ o' ℓ'} {C : Category o ℓ} {D : Category o' ℓ'} where
  private
    module C = Category C
    module D = Category D

  infixr 6 NaturalTransformation
  syntax NaturalTransformation F G = F ⇒ G

  record NaturalTransformation (F G : Functor C D) : Set (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    eta-equality
    private
      module F = Functor F
      module G = Functor G

    field
      η       : (X : C.Ob) → D.Hom (F.₀ X) (G.₀ X)
      natural : (X Y : C.Ob) (f : C.Hom X Y) → η Y D.∘ F.₁ f ≡ G.₁ f D.∘ η X

  open NaturalTransformation

  -- Identity natural transformation
  idNT : {F : Functor C D} → F ⇒ F
  η       idNT _     = Category.id D
  natural idNT X Y f = Category.id← D ∘p sym (Category.id→ D)

  -- Vertical composition
  _∘⇑_ : {F G H : Functor C D} → G ⇒ H → F ⇒ G → F ⇒ H
  η       (_∘⇑_ β α) X = η β X D.∘ η α X
  natural (_∘⇑_ {F = F} {G = G} {H = H} β α) X Y f =
    (β.η Y ∘ α.η Y) ∘ F.₁ f ≡⟨ assoc→ ⟩
    β.η Y ∘ α.η Y ∘ F.₁ f   ≡⟨ ap (β.η Y ∘_) (α.natural X Y f) ⟩
    β.η Y ∘ G.₁ f ∘ α.η X   ≡⟨ assoc← ⟩
    (β.η Y ∘ G.₁ f) ∘ α.η X ≡⟨ ap (_∘ α.η X) (β.natural X Y f) ⟩
    (H.₁ f ∘ β.η X) ∘ α.η X ≡⟨ assoc→ ⟩
    H.₁ f ∘ β.η X ∘ α.η X ∎
    where
      open PropReasoning
      open Category D

      module α = NaturalTransformation α
      module β = NaturalTransformation β

      module F = Functor F
      module G = Functor G
      module H = Functor H
