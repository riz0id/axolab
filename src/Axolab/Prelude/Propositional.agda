
module Axolab.Prelude.Propositional where

open import Axolab.Prelude.Primitive

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ₁
    B : Set ℓ₂
    C : Set ℓ₃

-- ---------------------------------------------------------------------------------------------------------------------

infix 4 _≡*_ _≡_

data _≡*_ {ℓ} {A : Set ℓ} (a : A) : {B : Set ℓ} → B → Set ℓ where
  instance refl : a ≡* a

_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
a ≡ b = a ≡* b

data _↝_ {ℓ : _} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl : a ↝ a

{-# BUILTIN EQUALITY _↝_ #-}

→rewrite : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ↝ y
→rewrite refl = refl

module PropReasoning where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : {ℓ : _} {A : Set ℓ} {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : {ℓ : _} {A : Set ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : {ℓ : _} {A : Set ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ refl ⟩ refl = refl

  _∎ : {ℓ : _} {A : Set ℓ} (x : A) → x ≡ x
  x ∎ = refl

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_∘p_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∘p refl = refl

ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

ap₂ : {w x : A} {y z : B} (f : A → B → C) → w ≡ x → y ≡ z → f w y ≡ f x z
ap₂ f refl refl = refl

subst : (P : A → Set ℓ₂) {x y : A} → x ≡ y → P x → P y
subst P refl x = x

UIP : {x y : A} (p q : x ≡ y) → p ≡ q
UIP refl refl = refl

postulate
  funExt : {B : A → Set ℓ₂} → {f g : (x : A) → B x} → ((x : A) → f x ≡* g x) → f ≡* g

funExtInvis : {ℓ ℓ' : _} {A : Set ℓ} {B : A → Set ℓ'} {f g : {x : A} → B x}
  → ((x : A) → f {x} ≡ g {x}) → _≡*_ {ℓ ⊔ ℓ'} {A = {x : A} → B x} f {B = {x : A} → B x} g
funExtInvis {ℓ} {ℓ'} {A} {B} {f} {g} p = ap fixup (funExt p) where
  fixup : ((x : A) → B x) → {x : A} → B x
  fixup f {x} = f x

record isContr {ℓ : _} (A : Set ℓ) : Set ℓ where
  constructor contract
  field
    center : A
    paths : (y : A) → center ≡ y

open isContr public
