module Prelude.Equality where

open import Prelude.Primitive

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Setoid ℓ₁
    B : Setoid ℓ₂
    C : Setoid ℓ₃

-- ---------------------------------------------------------------------------------------------------------------------

infix  4 _≡_
infixr 9 _∘p_

data _≡_ {ℓ : _} {A : Setoid ℓ} (x : A) : A → Setoid ℓ where
  refl : x ≡ x

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_∘p_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∘p refl = refl

ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

ap₂ : {w x : A} {y z : B} (f : A → B → C) → w ≡ x → y ≡ z → f w y ≡ f x z
ap₂ f refl refl = refl

subst : (P : A → Setoid ℓ₂) {x y : A} → x ≡ y → P x → P y
subst P refl x = x

UIP : {x y : A} (p q : x ≡ y) → p ≡ q
UIP refl refl = refl

module PropReasoning where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : {ℓ : _} {A : Setoid ℓ} {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : {ℓ : _} {A : Setoid ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : {ℓ : _} {A : Setoid ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ refl ⟩ refl = refl

  _∎ : {ℓ : _} {A : Setoid ℓ} (x : A) → x ≡ x
  x ∎ = refl

postulate
  funExt : {B : A → Setoid ℓ₂} → {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
