
module Axolab.Category.Instances.Algebras where

open import Axolab.Category
open import Axolab.Category.Functor
open import Axolab.Prelude

open Category
open PropReasoning

-- ---------------------------------------------------------------------------------------------------------------------

module _ {o ℓ} {C : Category o ℓ} where
  open import Axolab.Category.Functor.Algebra C

  private
    identity : {H : Endofunctor C} {F : Algebra H} → Homomorphism F F
    identity {H} {F} =
      record
        { homo     = C.id
        ; commutes =
          C.id C.∘ F.alg     ≡⟨ C.id← ⟩
          F.alg              ≡⟨ sym C.id→ ⟩
          F.alg C.∘ C.id     ≡⟨ ap (F.alg C.∘_) (sym H.F-id) ⟩
          F.alg C.∘ H.₁ C.id ∎
        }
      where
        module C = Category C
        module H = Functor H
        module F = Algebra F

    composition : {H : Endofunctor C} {X Y Z : Algebra H} → Homomorphism Y Z → Homomorphism X Y → Homomorphism X Z
    composition {H} {X} {Y} {Z} f g =
      record
        { homo     = f.homo C.∘ g.homo
        ; commutes =
          (f.homo C.∘ g.homo) C.∘ X.alg         ≡⟨ C.assoc→ ⟩
          f.homo C.∘ g.homo C.∘ X.alg           ≡⟨ ap (f.homo C.∘_) g.commutes ⟩
          f.homo C.∘ Y.alg C.∘ H.₁ g.homo       ≡⟨ C.assoc← ⟩
          (f.homo C.∘ Y.alg) C.∘ H.₁ g.homo     ≡⟨ ap (C._∘ H.₁ g.homo) f.commutes ⟩
          (Z.alg C.∘ H.₁ f.homo) C.∘ H.₁ g.homo ≡⟨ C.assoc→ ⟩
          Z.alg C.∘ H.₁ f.homo C.∘ H.₁ g.homo   ≡⟨ ap (Z.alg C.∘_) (sym (H.F-∘ _ _)) ⟩
          Z.alg C.∘ H.₁ (f.homo C.∘ g.homo)     ∎
        }
      where
        module C = Category C
        module H = Functor H

        module f = Homomorphism f
        module g = Homomorphism g

        module X = Algebra X
        module Y = Algebra Y
        module Z = Algebra Z

  _-Algebras : Endofunctor C → Category (o ⊔ ℓ) (o ⊔ ℓ)
  Ob     (F -Algebras) = Algebra F
  Hom    (F -Algebras) = Homomorphism 
  id     (F -Algebras) = identity
  _∘_    (F -Algebras) = composition
  id←    (F -Algebras) = {!id← C!}
  id→    (F -Algebras) = {!!}
  assoc← (F -Algebras) = {!!}
  assoc→ (F -Algebras) = {!!}
