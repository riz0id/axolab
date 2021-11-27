
module Axolab.Category.Functor.Instances.Free where

open import Axolab.Algebra.Theory
open import Axolab.Algebra.Theory.Instances.List
open import Axolab.Algebra.Theory.Structure.Monoid
open import Axolab.Category.Functor
open import Axolab.Category.Instances.Set
open import Axolab.Prelude
open import Axolab.Prelude.Primitive.Vect using (_∷_; nil)

open Functor

-- ---------------------------------------------------------------------------------------------------------------------

private
  id-map : ∀ {o} {A : Set o} (xs : List A) → map (λ x → x) xs ≡ xs
  id-map nil      = refl
  id-map (x ∷ xs) = ap (x ∷_) (id-map xs)

  ∘-map : ∀ {o} {A B C : Set o} (f : A → B) (g : B → C) (xs : List A) → map (λ x → g (f x)) xs ≡ map g (map f xs)
  ∘-map f g nil      = refl
  ∘-map f g (x ∷ xs) = ap (g (f x) ∷_) (∘-map f g xs)

  ++-map : ∀ {o} {A B : Set o} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
  ++-map f nil      ys = refl
  ++-map f (x ∷ xs) ys = ap (f x ∷_) (++-map f xs ys)

Free : {o : Level} → Functor (Set o) (Mon o)
F₀   Free = λ A →
  record { model  = List A
         ; models = list⊨monoid
         }
F₁   Free = λ f →
  record { function    = map f
         ; homomorphic =
           λ { unit nil              → refl
             ; ⨂    (xs ∷ ys ∷ nil)  → ++-map f xs ys } }
F-id Free = Homomorphism≡ id-map
F-∘  Free = λ g f → Homomorphism≡ (∘-map f g)

data NonDet : Set where
