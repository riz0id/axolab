module Axolab.Data.BinTree.Properties where

open import Axolab.Data.BinTree.Core
open import Axolab.Prelude
open import Axolab.Prelude.Function

private
  variable
    ℓ : Level
    A : Set ℓ

-- ---------------------------------------------------------------------------------------------------------------------

ap-bin : {a b : A} {X X' : Tree A} {Y Y' : Tree A} →
  X ≡ X' →
  a ≡ b  →
  Y ≡ Y' →
  Bin X a Y ≡ Bin X' b Y'
ap-bin {a = a} {b} {X} {X'} {Y} {Y'} X≡X' a≡a' Y≡Y' =
  Bin X  a Y  ≡⟨ ap (λ e → Bin X e Y)  a≡a' ⟩
  Bin X  b Y  ≡⟨ ap (λ e → Bin e b Y)  X≡X' ⟩
  Bin X' b Y  ≡⟨ ap (λ e → Bin X' b e) Y≡Y' ⟩
  Bin X' b Y' ∎
  where open PropReasoning

map-id : (X : Tree A) → map idf X ≡ X
map-id Tip         = refl
map-id (Bin l x r) = ap-bin (map-id l) refl (map-id r)

map-∘ : (f g : A → A) {X : Tree A} → map g (map f X) ≡ map (g ∘ f) X
map-∘ f g {Tip}       = refl
map-∘ f g {Bin l x r} = ap-bin (map-∘ f g) refl (map-∘ f g)
