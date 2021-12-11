
open import Axolab.Category
open import Axolab.Category.Functor

module Axolab.Category.Limit.Cone
  {o ℓ o' ℓ'} {C : Category o ℓ} {J : Category o' ℓ'}
  (F : Functor J C)
  where

open import Axolab.Prelude

private
  open module C = Category C

  module J = Category J
  module F = Functor F

  variable
    X Y : J.Ob

-- ---------------------------------------------------------------------------------------------------------------------

record Cone : Set (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  field
    apex    : Ob
    ψ       : (X : J.Ob) → Hom apex (F.₀ X)
    commute : {X Y : J.Ob} (f : J.Hom X Y) → F.₁ f ∘ ψ X ≡ ψ Y

open Cone

Cone≡ : {A B : Cone} → apex A ≡ apex B → (∀ o → ψ A o ≡* ψ B o) → A ≡ B
Cone≡ {A} {B} refl p = lemma (funExt p)
  where
    lemma : _≡*_ {A = (x : _) → Hom (apex A) (F.₀ x)} (ψ A) (ψ B) → A ≡ B
    lemma refl = lemma' (funExtInvis λ _ → funExtInvis λ _ → funExt λ _ → UIP _ _)
      where
        lemma' : _≡_ {A = {a b : _} (f : J.Hom a b) → F.₁ f ∘ ψ A a ≡ ψ B b} (commute A) (commute B) → A ≡* B
        lemma' refl = refl

record ConeHom (A B : Cone) : Set (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  field
    hom     : Hom (apex A) (apex B)
    commute : {o : _} → ψ B o ∘ hom ≡ ψ A o

open ConeHom

ConeHom≡ : {A B : Cone} {f g : ConeHom A B} → hom f ≡ hom g → f ≡ g
ConeHom≡ {A} {B} {f} {g} refl = lemma (funExtInvis λ _ → UIP _ _)
  where
    lemma : _≡_ {A = {o : _} → ψ B o ∘ hom g ≡ ψ A o} (commute f) (commute g) → f ≡ g
    lemma refl = refl

open Category

Cones : Category (o ⊔ ℓ ⊔ o' ⊔ ℓ') (o ⊔ ℓ ⊔ o' ⊔ ℓ')
Ob     Cones = Cone
Hom    Cones = ConeHom
id     Cones = record
  { hom     = C.id
  ; commute = C.id→
  }
_∘_    Cones = λ F G → record
  { hom     = hom F C.∘ hom G
  ; commute = (C.assoc← ∘p ap (C._∘ hom G) (commute F)) ∘p commute G
  }
id←    Cones = ConeHom≡ C.id←
id→    Cones = ConeHom≡ C.id→
assoc← Cones = ConeHom≡ C.assoc←
assoc→ Cones = ConeHom≡ C.assoc→
