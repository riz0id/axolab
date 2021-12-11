
module Axolab.Path where

open import Axolab.Type

open import Agda.Builtin.Cubical.Path public
open import Agda.Primitive.Cubical public
  renaming ( primIMin to _∨_; primIMax to _∧_; primINeg to ~_
           ; isOneEmpty to empty
           ; primComp to comp; primHComp to hcomp; primTransp to transp )

-- ---------------------------------------------------------------------------------------------------------------------

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP λ _ → A

refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = λ _ → x

sym : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)

subst : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) {x y : A} → x ≡ y → P x → P y
subst P p x = transp (λ i → P (p i)) i0 x

subst-filler : ∀ {ℓ₁ ℓ₂}
