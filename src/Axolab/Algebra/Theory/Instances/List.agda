
module Axolab.Algebra.Theory.Instances.List where

open import Axolab.Category
open import Axolab.Algebra.Theory
open import Axolab.Algebra.Theory.Structure.Monoid
open import Axolab.Prelude
open import Axolab.Prelude.Primitive.Vect using (_∷_; nil)

open Interpretation
open Model

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _++_

data List {o} (A : Setoid o) : Setoid o where
  nil : List A
  _∷_ : A → List A → List A

map : ∀ {o} {A B : Setoid o} → (A → B) → List A → List B
map f nil      = nil
map f (x ∷ xs) = f x ∷ map f xs

_++_ : ∀ {o} {A : Setoid o} → List A → List A → List A
nil      ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

list⊨monoid : ∀ {o} {A : Setoid o} → List A ⊨ monoid
interp list⊨monoid =
  λ { unit → nil
    ; ⨂    → λ f g → f ++ g }
sound (list⊨monoid {A = A}) =
  λ { associativity (xs ∷ ys ∷ zs ∷ nil) → ++-assoc← xs ys zs
    ; left-identity  _ → ++-id←
    ; right-identity _ → ++-id→ }
    where
      open PropReasoning

      ++-id← : {xs : List A} → nil ++ xs ≡ xs
      ++-id← = refl

      ++-id→ : {xs : List A} → xs ≡ xs ++ nil
      ++-id→ {nil}    = refl
      ++-id→ {x ∷ xs} = ap (x ∷_ ) ++-id→

      ++-assoc← : (xs ys zs : List A) → xs ++ ys ++ zs ≡ (xs ++ ys) ++ zs
      ++-assoc← xs ys nil =
        xs ++ ys ++ nil   ≡⟨ ap (xs ++_) (sym ++-id→) ⟩
        xs ++ ys          ≡⟨ ap (λ x → x) ++-id→ ⟩
        (xs ++ ys) ++ nil ∎
      ++-assoc← nil ys (z ∷ zs) = refl
      ++-assoc← (x ∷ xs) ys (z ∷ zs) = ap (x ∷_) (++-assoc← xs ys (z ∷ zs))
