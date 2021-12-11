
module Axolab.Algebra.Theory where

open import Axolab.Data.Product
open import Axolab.Data.Fin
open import Axolab.Data.Nat
open import Axolab.Data.Vec as Vec
open import Axolab.Prelude

open import Axolab.Algebra.Theory.Term public

-- ---------------------------------------------------------------------------------------------------------------------

record Theory (ℓ ℓ' : Level) : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    sig  : Signature ℓ
    laws       : Signature ℓ'
    laws-interp : ∀ {n} (l : laws n) → Term signature n × Term signature n

-- A # n ⇒ B is a function of n-many A into B.
--
_#_⇒_ : {ℓ : Level} → Set ℓ → (n : ℕ) → Set ℓ → Set ℓ
A # zero  ⇒ B = B
A # suc n ⇒ B = A → A # n ⇒ B

-- ⟦ S ⟧ A is an interpretation of S into A.
--
⟦_⟧ : ∀ {ℓ ℓ'} (S : Signature ℓ) (A : Set ℓ') → Set (ℓ ⊔ ℓ')
⟦ S ⟧ A = ∀ {m : ℕ} → S m → Vec A m → A

mutual
  private
    interpret' : ∀ {m n ℓ ℓ'} {S : Signature ℓ} {A : Set ℓ'} → ⟦ S ⟧ A → Vec A m → Vec (Term S m) n → Vec A n
    interpret' f env nil = nil
    interpret' f env (x ∷ xs) = interpret f x env ∷ interpret' f env xs

  interpret : ∀ {n ℓ ℓ'} {S : Signature ℓ} {A : Set ℓ'} → ⟦ S ⟧ A  → Term S n → Vec A n → A
  interpret f (var i)      xs = xs ‼ i
  interpret f (term op ys) xs = f op (interpret' f xs ys)

record Interpretation {o ℓ ℓ'} (A : Set o) (S : Theory ℓ ℓ') : Set (o ⊔ ℓ ⊔ ℓ') where
  open Theory S

  field
    eval  : ⟦ A ⟧ sig
    sound :
    -- (l : laws) (vars : Vect A (l-arities l)) →
    --   interpret interp vars (fst (l-relates l)) ≡ interpret interp vars (snd (l-relates l))


-- infix 4 Interpretation

-- record Theory (ℓ ℓ' : Level) : Set (lsuc (ℓ ⊔ ℓ')) where
--   field
--     signature : Signature ℓ
--     laws      : Set ℓ'

--   open Signature signature public

--   field
--     l-arities : laws → ℕ
--     l-relates : (l : laws) → Term signature (Fin (l-arities l)) × Term signature (Fin (l-arities l))

-- record Interpretation {o ℓ ℓ'} (A : Set o) (S : Theory ℓ ℓ') : Set (o ⊔ ℓ ⊔ ℓ') where
--   open Theory S

--   field
--     interp : Interprets A signature
--     sound  : (l : laws) (vars : Vect A (l-arities l)) →
--       interpret interp vars (fst (l-relates l)) ≡ interpret interp vars (snd (l-relates l))

-- syntax Interpretation A S = A ⊨ S

-- record Model {ℓ ℓ'} (S : Theory ℓ ℓ') (o : Level) : Set (lsuc o ⊔ ℓ ⊔ ℓ') where
--   field
--     model  : Set o
--     models : model ⊨ S

--   open Interpretation models public

-- record Homomorphism {o o' ℓ ℓ'} (S : Theory o o') (M : Model S ℓ) (M' : Model S ℓ') : Set (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
--   private
--     module S = Theory S

--     module Dom = Model M
--     module Cod = Model M'

--   field
--     function    : Dom.model → Cod.model
--     homomorphic : (o : {!!}) (args : Vect Dom.model (S.arities o)) →
--       function (Dom.interp o $⟨ args ⟩) ≡ Cod.interp o $⟨ Vect.map function args ⟩

-- open Homomorphism

-- Homomorphism≡ : ∀ {o ℓ o' ℓ'} {S : Theory ℓ ℓ'} {M : Model S o} {M' : Model S o'} {H H' : Homomorphism S M M'}
--   → (∀ x → function H x ≡ function H' x) → H ≡* H'
-- Homomorphism≡ {H  = record { function = _; homomorphic = r}}
--               {H' = record { function = _; homomorphic = s}}
--               p
--   rewrite →rewrite (funExt p)
--   rewrite →rewrite (funExt λ o → funExt λ a → UIP (r o a) (s o a))
--   = refl
