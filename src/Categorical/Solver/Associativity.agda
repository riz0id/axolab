
open import Categorical.Category

module Categorical.Solver.Associativity {o ℓ} (C : Category o ℓ) where

open import Prelude
open import Prelude.Equality

private
  variable
    ℓ₁ ℓ₂ : Level

-- ---------------------------------------------------------------------------------------------------------------------

infixr 9 _∙_

open Category C

data Tm : Ob → Ob → Setoid (o ⊔ ℓ) where
  idt : {X : Ob} → Tm X X
  ⟦_⟧ : {X Y : Ob} → Hom X Y → Tm X Y
  _∙_ : {X Y Z : Ob} → Tm Y Z → Tm X Y → Tm X Z

embed : {A B : _} → Tm A B → Hom A B
embed idt     = id
embed ⟦ t ⟧   = t
embed (t ∙ u) = embed t ∘ embed u

eval : {A B C : Ob} → Tm B C → Hom A B → Hom A C
eval idt     f = f
eval ⟦ t ⟧   f = t ∘ f
eval (t ∙ u) f = eval t (eval u f)

eval≡ : {A B : Ob} (e : Tm A B) → eval e id ≡ embed e
eval≡ idt     = refl
eval≡ ⟦ t ⟧   = id→
eval≡ (t ∙ u) =
  eval t (eval u id)    ≡⟨ sym (lemma t (eval u id)) ⟩
  eval t id ∘ eval u id ≡⟨ ap₂ _∘_ (eval≡ t) (eval≡ u) ⟩
  embed (t ∙ u)         ∎
  where
    open PropReasoning

    lemma : {A B C : Ob} (e : Tm B C) (f : Hom A B) → eval e id ∘ f ≡ eval e f
    lemma idt     f = id←
    lemma ⟦ t ⟧   f = ap (_∘ f) id→
    lemma (t ∙ u) f =
      eval t (eval u id) ∘ f      ≡⟨ ap (_∘ f) (sym (lemma t (eval u id))) ⟩
      (eval t id ∘ eval u id) ∘ f ≡⟨ assoc→ ⟩
      eval t id ∘ eval u id ∘ f   ≡⟨ ap (_ ∘_) (lemma u f) ⟩
      eval t id ∘ eval u f        ≡⟨ lemma t (eval u f) ⟩
      eval (t ∙ u) f              ∎

associateSolve : {A B : Ob} (f g : Tm A B) → eval f id ≡ eval g id → embed f ≡ embed g
associateSolve f g p = sym (eval≡ f) ∘p p ∘p eval≡ g

syntax associateSolve f g p = associate p ∥ f ∥ g
