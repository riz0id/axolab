
module Axolab.Algebra.Theory where

open import Axolab.Algebra.Theory.Signature public
open import Axolab.Algebra.Theory.Term public
open import Axolab.Data.Fin
open import Axolab.Data.Nat.Core
open import Axolab.Data.Product
open import Axolab.Data.Vect as Vect
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

infix 4 Interpretation

record Theory (ℓ ℓ' : Level) : Setoid (lsuc (ℓ ⊔ ℓ')) where
  field
    signature : Signature ℓ
    laws      : Setoid ℓ'

  open Signature signature public

  field
    l-arities : laws → ℕ
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
      function (Dom.interp o args) ≡ Cod.interp o (Vect.map function args)
