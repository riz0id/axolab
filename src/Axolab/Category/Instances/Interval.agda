
module Axolab.Category.Instances.Interval where

open import Axolab.Category
open import Axolab.Data.Bool
open import Axolab.Data.Bot
open import Axolab.Data.Top
open import Axolab.Prelude

open Category

-- ---------------------------------------------------------------------------------------------------------------------

infixr 5 _𝟚⇒_

data _𝟚⇒_ : Bool → Bool → Set where
  I⇒I : ∀ {e} → e 𝟚⇒ e
  𝟘⇒𝟙 : false 𝟚⇒ true

Interval : Category 0ℓ 0ℓ
Interval = cat where
  _𝟚∘_ : {X Y Z : Bool} → Y 𝟚⇒ Z → X 𝟚⇒ Y → X 𝟚⇒ Z
  _𝟚∘_ I⇒I I⇒I = I⇒I
  _𝟚∘_ I⇒I 𝟘⇒𝟙 = 𝟘⇒𝟙
  _𝟚∘_ 𝟘⇒𝟙 I⇒I = 𝟘⇒𝟙

  𝟚⇠id : {X Y : Bool} (f : X 𝟚⇒ Y) → I⇒I 𝟚∘ f ≡ f
  𝟚⇠id I⇒I = refl
  𝟚⇠id 𝟘⇒𝟙 = refl

  𝟚→id : {X Y : Bool} (f : X 𝟚⇒ Y) → f 𝟚∘ I⇒I ≡ f
  𝟚→id I⇒I = refl
  𝟚→id 𝟘⇒𝟙 = refl

  𝟚⇠assoc : ∀ {X Y Z W} (f : X 𝟚⇒ Y) (g : Y 𝟚⇒ Z) (h : Z 𝟚⇒ W) → (h 𝟚∘ (g 𝟚∘ f)) ≡ ((h 𝟚∘ g) 𝟚∘ f)
  𝟚⇠assoc I⇒I I⇒I I⇒I = refl
  𝟚⇠assoc 𝟘⇒𝟙 I⇒I I⇒I = refl
  𝟚⇠assoc I⇒I I⇒I 𝟘⇒𝟙 = refl
  𝟚⇠assoc I⇒I 𝟘⇒𝟙 I⇒I = refl

  𝟚→assoc : ∀ {X Y Z W} (f : X 𝟚⇒ Y) (g : Y 𝟚⇒ Z) (h : Z 𝟚⇒ W) → ((h 𝟚∘ g) 𝟚∘ f) ≡ (h 𝟚∘ (g 𝟚∘ f))
  𝟚→assoc I⇒I I⇒I I⇒I = refl
  𝟚→assoc 𝟘⇒𝟙 I⇒I I⇒I = refl
  𝟚→assoc I⇒I I⇒I 𝟘⇒𝟙 = refl
  𝟚→assoc I⇒I 𝟘⇒𝟙 I⇒I = refl

  cat : Category 0ℓ 0ℓ
  Ob     cat = Bool
  Hom    cat = _𝟚⇒_
  id     cat = I⇒I
  _∘_    cat = _𝟚∘_
  id←    cat = 𝟚⇠id _
  id→    cat = 𝟚→id _
  assoc← cat = 𝟚⇠assoc _ _ _
  assoc→ cat = 𝟚→assoc _ _ _
