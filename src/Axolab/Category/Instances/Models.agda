
module Axolab.Category.Instances.Models where

open import Axolab.Algebra.Theory
open import Axolab.Category
open import Axolab.Prelude
open import Axolab.Prelude.Primitive.Nary
open import Axolab.Prelude.Primitive.Vect as Vect

open Category
open Homomorphism
open Model

-- ---------------------------------------------------------------------------------------------------------------------

_-Models : {s ℓ ℓ' : Level} → Theory ℓ ℓ' → Category (lsuc s ⊔ ℓ ⊔ ℓ') (s ⊔ ℓ ⊔ ℓ')
_-Models {s} S = cat where
  module S = Theory S

  apVectId : ∀ {ℓ n} {A : Set ℓ} (xs : Vect A n) → map (λ x → x) xs ≡ xs
  apVectId nil      = refl
  apVectId (x ∷ xs) = ap (x ∷_) (apVectId xs)

  apVect∘ : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
    → (g : B → C) (f : A → B) (xs : Vect A n) → map (λ x → g (f x)) xs ≡ map g (map f xs)
  apVect∘ _ _ nil      = refl
  apVect∘ _ _ (x ∷ xs) = ap (_ ∷_) (apVect∘ _ _ xs)

  cat : Category _ _
  Ob     cat = Model S s
  Hom    cat = Homomorphism S
  id     cat {X} =
    record { function    = λ x → x
           ; homomorphic = λ ops args → ap (λ e → interp X ops $⟨ e ⟩) (sym (apVectId args)) }
  _∘_    cat {X} {Y} {Z} f g =
    record { function    = λ x → f.function (g.function x)
           ; homomorphic = homomorphic∘ }
    where
      module f = Homomorphism f
      module g = Homomorphism g

      homomorphic∘ : ∀ ops args
        → f.function (g.function (interp X ops $⟨ args ⟩))
        ≡ interp Z ops $⟨ map (λ x → f.function (g.function x)) args ⟩
      homomorphic∘ ops args
        rewrite →rewrite (g.homomorphic ops args)
        rewrite →rewrite (f.homomorphic ops (map g.function args))
        rewrite →rewrite (sym (apVect∘ f.function g.function args)) = refl
  id←    cat = Homomorphism≡ λ _ → refl
  id→    cat = Homomorphism≡ λ _ → refl
  assoc← cat = Homomorphism≡ λ _ → refl
  assoc→ cat = Homomorphism≡ λ _ → refl
