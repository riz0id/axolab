
module Axolab.Category.Limit where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Category.Object.Terminal
open import Axolab.Prelude

open import Axolab.Category.Limit.Cone public

open Cone
open Terminal

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level

    J : Category o₁ ℓ₁
    D : Category o₃ ℓ₃
    C : Category o₂ ℓ₂

-- ---------------------------------------------------------------------------------------------------------------------

Limit : {J : Category o₁ ℓ₁} {C : Category o₂ ℓ₂} → Functor J C → Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂)
Limit F = Terminal (Cones F)

module _ {F : Functor J C} (G : Functor C D) where
  open PropReasoning

  private
    module J = Category J
    module C = Category C
    module D = Category D

    module F = Functor F
    module G = Functor G

  mapCone : Cone F → Cone (G F∘ F)
  apex    (mapCone c)   = G.₀ (apex c)
  ψ       (mapCone c) X = G.₁ (ψ c X)
  commute (mapCone c) {X = X} {Y = Y} f =
    G.₁ (F.₁ f) D.∘ G.₁ (ψ c X) ≡⟨ sym (G.F-∘ (F.₁ f) (ψ c X)) ⟩
    G.₁ (F.₁ f C.∘ ψ c X)       ≡⟨ ap G.₁ (commute c f) ⟩
    G.₁ (ψ c Y)                 ∎

  PreservesLimit : Limit F → Set _
  PreservesLimit lim = isContr ({A : Cone _} → ConeHom (G F∘ F) A (mapCone (⊤ lim)))

module _ {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃ : Level} {C : Category o₂ ℓ₂} {D : Category o₃ ℓ₃} where

  Continuous : Functor C D → Set (lsuc (o₁ ⊔ ℓ₁) ⊔ o₂ ⊔ ℓ₂ ⊔ o₃ ⊔ ℓ₃)
  Continuous F = {J : Category o₁ ℓ₁} {dia : Functor J C} (L : Limit dia) → PreservesLimit F L
