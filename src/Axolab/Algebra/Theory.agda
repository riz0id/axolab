
module Axolab.Algebra.Theory where

open import Axolab.Data.Product
open import Axolab.Prelude.Primitive.Fin
open import Axolab.Prelude.Primitive.Nary
open import Axolab.Prelude.Primitive.Nat
open import Axolab.Prelude.Primitive.Vect as Vect
open import Axolab.Prelude

open import Axolab.Algebra.Theory.Signature public
open import Axolab.Algebra.Theory.Term public

-- ---------------------------------------------------------------------------------------------------------------------

infix 4 Interpretation

record Theory (ℓ ℓ' : Level) : Setoid (lsuc (ℓ ⊔ ℓ')) where
  field
    signature : Signature ℓ
    laws      : Setoid ℓ'

  open Signature signature public

  field
    l-arities : laws → Nat
    l-relates : (l : laws) → Term signature (Fin (l-arities l)) × Term signature (Fin (l-arities l))

record Interpretation {o ℓ ℓ'} (A : Setoid o) (S : Theory ℓ ℓ') : Setoid (o ⊔ ℓ ⊔ ℓ') where
  open Theory S

  field
    interp : Interprets A signature
    sound  : (l : laws) (vars : Vect A (l-arities l)) →
      evaluate interp vars (fst (l-relates l)) ≡ evaluate interp vars (snd (l-relates l))

syntax Interpretation A S = A ⊨ S

record Model {ℓ ℓ'} (S : Theory ℓ ℓ') (o : Level) : Setoid (lsuc o ⊔ ℓ ⊔ ℓ') where
  field
    model  : Setoid o
    models : model ⊨ S

  open Interpretation models public

record Homomorphism {o o' ℓ ℓ'} (S : Theory o o') (M : Model S ℓ) (M' : Model S ℓ') : Setoid (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
  private
    module S = Theory S

    module Dom = Model M
    module Cod = Model M'

  field
    function    : Dom.model → Cod.model
    homomorphic : (o : S.operations) (args : Vect Dom.model (S.o-arities o)) →
      function (Dom.interp o $⟨ args ⟩) ≡ Cod.interp o $⟨ Vect.map function args ⟩

open Homomorphism

Homomorphism≡ : ∀ {o ℓ o' ℓ'} {S : Theory ℓ ℓ'} {M : Model S o} {M' : Model S o'} {H H' : Homomorphism S M M'}
  → (∀ x → function H x ≡ function H' x) → H ≡* H'
Homomorphism≡ {H  = record { function = _; homomorphic = r}}
              {H' = record { function = _; homomorphic = s}}
              p
  rewrite →rewrite (funExt p)
  rewrite →rewrite (funExt λ o → funExt λ a → UIP (r o a) (s o a))
  = refl
