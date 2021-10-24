
open import Categorical.Category

module Categorical.Category.Structure.CartesianClosed {o ℓ} (C : Category o ℓ) where

open import Categorical.Category.Structure.Cartesian
open import Categorical.Solver.Associativity C using (associateSolve; ⟦_⟧; _∙_)
open import Categorical.Functor
open import Categorical.Bifunctor
open import Categorical.Object.Terminal
open import Prelude
open import Prelude.Data.Product using ( _,_; fst; snd )
open import Prelude.Equality

open Category C
open Functor

private
  variable
    A B X Y Z : Ob

-- ---------------------------------------------------------------------------------------------------------------------

record CartesianClosed (Ca : Cartesian C) : Setoid (o ⊔ ℓ) where
  private
    open module Ca  = Cartesian Ca
    open module -×- = Functor -×-

  field
    [_,_] : Ob → Ob → Ob
    eval  : {A B : Ob} → Hom ([ A , B ] ×₀ A) B

  uncurry : Hom X [ Y , Z ] → Hom (X ×₀ Y) Z
  uncurry f = eval ∘ first -×- f

  field
    λf       : Hom (A ×₀ B) X → Hom A [ B , X ]
    β        : (g : Hom (A ×₀ B) X) → uncurry (λf g) ≡ g
    λ-unique : {g : Hom (A ×₀ B) X} (h : Hom A [ B , X ]) → uncurry h ≡ g → h ≡ λf g

  open PropReasoning

  λ-ap : {f g : Hom (A ×₀ B) X} → f ≡ g → λf f ≡ λf g
  λ-ap refl = refl

  λ-η : λf (eval {A} {B}) ≡ id
  λ-η = sym (λ-unique _ p) where
    p = eval ∘ first -×- id ≡⟨ ap (eval ∘_) (F-id -×-) ⟩
        eval ∘ id           ≡⟨ id→ ⟩
        eval                ∎

  λ-unique₂ : {f g : Hom X [ A , B ]} → eval {A} {B} ∘ first -×- f ≡ eval {A} {B} ∘ first -×- g → f ≡ g
  λ-unique₂ eq = λ-unique _ eq ∘p sym (λ-unique _ refl)
