
open import Axolab.Category
open import Axolab.Category.Structure.Cartesian

module Axolab.Category.Constructions.Ideal
  {o ℓ} {C : Category o ℓ}
  (Ca : Cartesian (C ^op))
  where

open import Axolab.Category.Instances.Product
open import Axolab.Category.Instances.Set
open import Axolab.Category.Constructions.Monad
open import Axolab.Category.Functor
open import Axolab.Category.Functor.Bifunctor
open import Axolab.Category.Functor.Hom
open import Axolab.Category.NaturalTransformation
open import Axolab.Data.Coproduct
open import Axolab.Prelude

open Cartesian Ca
  renaming ( _×₀_ to _+₀_; _×₁_ to _+₁_
           ; -×- to -+-; _×- to _+-; -×_ to -+_
           ; ⊤ to ⊥; π₁ to inj₁; π₂ to inj₂
           ; π₁×π₂≡id to inj₁+inj₂≡id; π₁×₁≡id to +₁inj₁≡id; π₂×₁≡id to +₁inj₂≡id
           ; ×₁-distrib to +₁-distrib )
open Category C
open Functor
open Monad
open NaturalTransformation

-- ---------------------------------------------------------------------------------------------------------------------


-+_- : Endofunctor C → Endofunctor C
F₀   -+ F - = λ X → X +₀ F₀ F X
F₁   -+ F - = λ f → inj₁ ∘ f +₁ inj₂ ∘ F₁ F f
F-id -+ F - =
  inj₁ ∘ id +₁ inj₂ ∘ F.₁ id ≡⟨ ap (λ e → _ +₁ inj₂ ∘ e) F.F-id ⟩
  inj₁ ∘ id +₁ inj₂ ∘ id     ≡⟨ ap₂ _+₁_ id→ id→ ⟩
  inj₁ +₁ inj₂               ≡⟨ inj₁+inj₂≡id ⟩
  id ∎
  where
    module F = Functor F
    open PropReasoning
F-∘  -+ F - f g =
  inj₁ ∘ f ∘ g +₁ inj₂ ∘ F.₁ (f ∘ g)                      ≡⟨ ap (λ e → _ +₁ inj₂ ∘ e) (F.F-∘ f g) ⟩
  inj₁ ∘ f ∘ g +₁ inj₂ ∘ F.₁ f ∘ F.₁ g                    ≡⟨ F-∘ -+- _ _ ⟩
  (inj₁ ∘ f +₁ inj₂ ∘ F.₁ f) ∘ (inj₁ ∘ g +₁ inj₂ ∘ F.₁ g) ∎
  where
    module F = Functor F
    open PropReasoning

record Ideal : Set (o ⊔ ℓ) where
  field
    T     : Endofunctor C
    ideal : (T F∘ -+ T -) ⇒ T

  module ideal = NaturalTransformation ideal

  module T    = Functor T
  module -+T- = Functor -+ T -

  idealMonad : Monad C
  M      idealMonad = -+ T -
  unit   idealMonad .η       = λ _ → inj₁
  unit   idealMonad .natural = λ _ _ _ → sym (+₁inj₁≡id)
  mult   idealMonad .η       = λ X → id +₁ inj₂ ∘ ideal.η X
  mult   idealMonad .natural = λ X Y f →
    (id +₁ inj₂ ∘ ideal.η Y) ∘ (inj₁ ∘ -+T-.₁ f +₁ inj₂ ∘ T.₁ (-+T-.₁ f)) ≡⟨ +₁-distrib _ _ _ ⟩
    (id +₁ inj₂ ∘ ideal.η Y) ∘ inj₁ ∘ -+T-.₁ f +₁ (id +₁ inj₂ ∘ ideal.η Y) ∘ inj₂ ∘ T.₁ (-+T-.₁ f)
      ≡⟨ ap (λ e → e +₁ (id +₁ inj₂ ∘ ideal.η Y) ∘ inj₂ ∘ T.₁ (-+T-.₁ f)) (lemma-inj₁ Y f) ⟩
    -+T-.₁ f +₁ (id +₁ inj₂ ∘ ideal.η Y) ∘ inj₂ ∘ T.₁ (-+T-.₁ f) ≡⟨ ap (-+T-.₁ f +₁_) assoc← ⟩
    -+T-.₁ f +₁ ((id +₁ inj₂ ∘ ideal.η Y) ∘ inj₂) ∘ T.₁ (-+T-.₁ f)
      ≡⟨ ap (λ e → -+T-.₁ f +₁ e ∘ T.₁ (-+T-.₁ f)) +₁inj₂≡id ⟩
    -+T-.₁ f +₁ (inj₂ ∘ ideal.η Y) ∘ T.₁ (-+T-.₁ f) ≡⟨ ap (λ e → -+T-.₁ f +₁ e) assoc→ ⟩
    -+T-.₁ f +₁ inj₂ ∘ (ideal.η Y ∘ T.₁ (-+T-.₁ f)) ≡⟨ ap (λ e → -+T-.₁ f +₁ inj₂ ∘ e) (ideal.natural X Y f) ⟩
    (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) +₁ inj₂ ∘ T.₁ f ∘ ideal.η X ≡⟨ ap ((inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) +₁_) assoc← ⟩
    (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) +₁ (inj₂ ∘ T.₁ f) ∘ ideal.η X
      ≡⟨ ap (λ e → (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) +₁ e ∘ ideal.η X) (sym +₁inj₂≡id) ⟩
    (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) +₁ ((inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) ∘ inj₂) ∘ ideal.η X
      ≡⟨ ap (λ e → (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) +₁ e) assoc→ ⟩
    (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) +₁ (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) ∘ inj₂ ∘ ideal.η X
      ≡⟨ ap (λ e → e +₁ (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) ∘ inj₂ ∘ ideal.η X) (sym id→) ⟩
    (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) ∘ id +₁ (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) ∘ inj₂ ∘ ideal.η X ≡⟨ sym (+₁-distrib _ _ _) ⟩
    (inj₁ ∘ f +₁ inj₂ ∘ T.₁ f) ∘ (id +₁ inj₂ ∘ ideal.η X) ∎
    where
      open PropReasoning

      lemma-inj₁ : ∀ {X} (Y : Ob) (f : Hom X Y)
        → (id +₁ inj₂ ∘ ideal.η Y) ∘ inj₁ ∘ -+T-.₁ f ≡ -+T-.₁ f
      lemma-inj₁ Y f =
        (id +₁ inj₂ ∘ ideal.η Y) ∘ inj₁ ∘ -+T-.₁ f   ≡⟨ assoc← ⟩
        ((id +₁ inj₂ ∘ ideal.η Y) ∘ inj₁) ∘ -+T-.₁ f ≡⟨ ap (_∘ -+T-.₁ f) +₁inj₁≡id ⟩
        id ∘ -+T-.₁ f                                ≡⟨ id← ⟩
        -+T-.₁ f ∎
  ident← idealMonad = {!!}
  ident→ idealMonad = {!!}
  assoc  idealMonad = {!!}


-- -+_- : Endofunctor (C ^op) → Endofunctor (C ^op)
-- -+ F - = -+ (F₀ F ⊥)

-- _[-+T-] : Endofunctor (C ^op) → Endofunctor (C ^op)
-- T [-+T-] =
--   record
--     { F₀   = T+₀
--     ; F₁   = T+₁
--     ; F-id = T+id
--     ; F-∘  = T+∘
--     }
--   where
--     module T = Functor T

--     open PropReasoning

--     T+₀ : C.Ob → C.Ob
--     T+₀ X = T.₀ (X +₀ T.₀ X)

--     T+₁ : {X Y : C.Ob} → C^op.Hom X Y → C^op.Hom (T+₀ X) (T+₀ Y)
--     T+₁ f = T.₁ (inj₁ C.∘ f +₁ inj₂ C.∘ T.₁ f)

--     T+id : {X : C.Ob} → T+₁ (C.id {X}) ≡ C.id
--     T+id =
--       T.₁ (inj₁ C.∘ C.id +₁ inj₂ C.∘ T.₁ C.id) ≡⟨ ap (λ e → T.₁ (inj₁ C.∘ C.id +₁ inj₂ C.∘ e)) (F-id T) ⟩
--       T.₁ (inj₁ C.∘ C.id +₁ inj₂ C.∘ C.id)     ≡⟨ ap₂ (λ e₁ e₂ → T.₁ (e₁ +₁ e₂)) C.id→ C.id→ ⟩
--       T.₁ (inj₁ +₁ inj₂)                       ≡⟨ ap T.₁ inj₁+inj₂≡id ⟩
--       T.₁ C.id                                 ≡⟨ F-id T ⟩
--       C.id                                     ∎

--     T+∘ : ∀ {X Y Z} (g : C.Hom Z Y) (f : C.Hom Y X) → T+₁ (f C.∘ g) ≡ T+₁ f C.∘ T+₁ g
--     T+∘ g f =
--       T.₁ (inj₁ C.∘ f C.∘ g +₁ inj₂ C.∘ T.₁ (f C.∘ g))                          ≡⟨ ap (λ e → T.₁ (inj₁ C.∘ _ +₁ inj₂ C.∘ e)) (F-∘ T g f) ⟩
--       T.₁ (inj₁ C.∘ f C.∘ g +₁ inj₂ C.∘ T.₁ f C.∘ T.₁ g)                        ≡⟨ ap T.₁ (F-∘ -+- _ _) ⟩
--       T.₁ ((inj₁ C.∘ f +₁ inj₂ C.∘ T.₁ f) C.∘ (inj₁ C.∘ g +₁ inj₂ C.∘ T.₁ g))   ≡⟨ F-∘ T _ _ ⟩
--       T.₁ (inj₁ C.∘ f +₁ inj₂ C.∘ T.₁ f) C.∘ T.₁ (inj₁ C.∘ g +₁ inj₂ C.∘ T.₁ g) ∎


-- record Ideal : Set (o ⊔ ℓ) where
--   field
--     T      : Endofunctor (C ^op)
--     counit : (T F∘ -+ T -) ⇒ T

--   private
--     module T = Functor T


-- module _ (ideal : Ideal) where
--   open Ideal ideal using (T)
--   open Monad

--   module T = Functor T
--   module T[-+T-] = Functor (T [-+T-])

--   private
--     T[-+T-]-η : (X : C.Ob) → C.Hom (T.₀ (X +₀ T.₀ X)) X
--     T[-+T-]-η X = {!!}

--     idealUnit : Id ⇒ T [-+T-]
--     η       idealUnit = T[-+T-]-η
--     natural idealUnit = {!!}

--   Ideal⇒Monad : Monad C
--   M      Ideal⇒Monad = {!!} -- T [-+T-]
--   unit   Ideal⇒Monad = {!!}
--   mult   Ideal⇒Monad = {!!}
--   ident← Ideal⇒Monad = {!!}
--   ident→ Ideal⇒Monad = {!!}
--   assoc  Ideal⇒Monad = {!!}
