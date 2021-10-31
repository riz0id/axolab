
module Axolab.Category.Functor where

open import Axolab.Category
open import Axolab.Category.Functor.Core public
open import Axolab.Prelude

open Category
open Functor

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level
    C : Category o₁ ℓ₁
    D : Category o₂ ℓ₂
    E : Category o₃ ℓ₃

-- ---------------------------------------------------------------------------------------------------------------------

Functor≡ : {F G : Functor C D} → F₀ F ≡ F₀ G → (∀ {X Y} (f : Hom C X Y) → F₁ F f ≡* F₁ G f) → F ≡ G
Functor≡ {o₁} {ℓ₁} {C} {o₂} {ℓ₂} {D} {F} {G} refl p =
  lemma (funExtInvis λ _ → funExtInvis λ _ → funExt λ f → p f)
  where
    module C = Category C
    module D = Category D

    module F = Functor F
    module G = Functor G

    rep : Functor C D → Setoid (o₁ ⊔ ℓ₁ ⊔ ℓ₂)
    rep H = {A B : C.Ob} (f : C.Hom A B) → D.Hom (Functor.F₀ H A) (Functor.F₀ H B)

    Fid≡ : Functor C D → Setoid (o₁ ⊔ ℓ₂)
    Fid≡ H = {x : C.Ob} → Functor.F₁ H (C.id {x}) ≡ D.id {Functor.F₀ H x}

    F∘≡ : Functor C D → Setoid _
    F∘≡ H = ∀ {X Y Z} (f : C.Hom Y Z) (g : C.Hom X Y) → Functor.F₁ H (f C.∘ g) ≡ Functor.F₁ H f D.∘ Functor.F₁ H g

    F₁≡ : _≡*_ {_} {A = rep F} F.₁ {B = rep G} G.₁
    F₁≡ = funExtInvis λ x → funExtInvis λ y → funExt λ f → p f

    lemma : _≡*_ {_} {A = rep F} F.₁ {B = rep G} G.₁ → F ≡* G
    lemma refl = go (funExtInvis λ _ → UIP _ _) q where
      q = funExtInvis λ _ → funExtInvis λ _ → funExtInvis λ _ → funExt λ _ → funExt λ _ → UIP _ _

      go : _≡*_ {_} {A = Fid≡ F} F.F-id {B = Fid≡ G} G.F-id
        → _≡*_ {_} {A = F∘≡ F} (Functor.F-∘ F) {B = F∘≡ G} (Functor.F-∘ G)
        → F ≡* G
      go refl refl = refl

module _ {C : Category o₁ ℓ₁} {D : Category o₂ ℓ₂} {E : Category o₃ ℓ₃} where
  infixr 6 _F∘_

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
