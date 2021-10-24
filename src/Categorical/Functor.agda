module Categorical.Functor where

open import Categorical.Category
open import Categorical.Functor.Core public
open import Prelude
open import Prelude.Equality

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level

-- ---------------------------------------------------------------------------------------------------------------------

open Functor

Endofunctor : ∀ {o ℓ} (C : Category o ℓ) → Setoid (o ⊔ ℓ)
Endofunctor C = Functor C C

Id : ∀ {o ℓ} {C : Category o ℓ} → Functor C C
F₀   Id x   = x
F₁   Id f   = f
F-id Id     = refl
F-∘  Id _ _ = refl

module _ {C : Category o₁ ℓ₁} {D : Category o₂ ℓ₂} {E : Category o₃ ℓ₃} where
  private
    module C = Category C
    module D = Category D
    module E = Category E

  open PropReasoning

  _F∘_ : Functor D E → Functor C D → Functor C E
  _F∘_ G F =
    record
      { F₀   = GF₀
      ; F₁   = GF₁
      ; F-id = GF-id
      ; F-∘  = GF-∘
      }
    where
      module F = Functor F
      module G = Functor G

      GF₀ : C.Ob → E.Ob
      GF₀ X = G.₀ (F.₀ X)

      GF₁ : {X Y : C.Ob} → C.Hom X Y → E.Hom (GF₀ X) (GF₀ Y)
      GF₁ X = G.₁ (F.₁ X)

      GF-id : {X : C.Ob} → GF₁ C.id ≡ E.id {GF₀ X}
      GF-id {X} =
        GF₁ C.id ≡⟨ ap G.₁ F.F-id ⟩
        G.₁ D.id ≡⟨ G.F-id ⟩
        E.id     ∎

      GF-∘ : {X Y Z : C.Ob} (g : C.Hom Y Z) (f : C.Hom X Y) → GF₁ (g C.∘ f) ≡ GF₁ g E.∘ GF₁ f
      GF-∘ g f =
        GF₁ (g C.∘ f)         ≡⟨ ap G.₁ (F.F-∘ g f) ⟩
        G.₁ (F.₁ g D.∘ F.₁ f) ≡⟨ G.F-∘ (F.₁ g) (F.₁ f) ⟩
        GF₁ g E.∘ GF₁ f       ∎
