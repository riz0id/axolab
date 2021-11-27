
module Axolab.Algebra.Operad where

open import Axolab.Data.Fin
open import Axolab.Data.Nat
open import Axolab.Data.Product
open import Axolab.Data.Vec
open import Axolab.Prelude

-- ---------------------------------------------------------------------------------------------------------------------

Signature : (ℓ : Level) → Set (lsuc ℓ)
Signature ℓ = @0 ℕ → Set ℓ

Laws : (ℓ : Level) → Set (lsuc ℓ)
Laws ℓ = ℕ → Set ℓ

data Term {ℓ} (S : Signature ℓ) : @0 ℕ → Set ℓ where
  var  : {n   : ℕ} → Fin n → Term S n
  term : {m n : ℕ} → S m → Vec (Term S n) m → Term S n

record Theory (ℓ ℓ' : Level) : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    signature  : Signature ℓ
    laws       : Signature ℓ'
    laws-interp : ∀ {n} (l : laws n) → Term signature n × Term signature n

_#_⇒_ : {ℓ : Level} → Set ℓ → (n : ℕ) → Set ℓ → Set ℓ
A # zero  ⇒ B = B
A # suc n ⇒ B = A → A # n ⇒ B

⟦_⟧ : ∀ {ℓ ℓ'} (S : Signature ℓ) (A : Set ℓ') → Set (ℓ ⊔ ℓ')
⟦ S ⟧ A = ∀ {m : ℕ} → S m → Vec A m → A

mutual
  private
    evaluate' : ∀ {m n ℓ ℓ'} {S : Signature ℓ} {A : Set ℓ'} → ⟦ S ⟧ A → Vec A m → Vec (Term S m) n → Vec A n
    evaluate' f env nil = nil
    evaluate' f env (x ∷ xs) = evaluate f x env ∷ evaluate' f env xs

  evaluate : ∀ {n ℓ ℓ'} {S : Signature ℓ} {A : Set ℓ'} → ⟦ S ⟧ A  → Term S n → Vec A n → A
  evaluate f (var i)      xs = xs ‼ i
  evaluate f (term op ys) xs = f op (evaluate' f xs ys)

data Op (ℓ : Level) : Signature ℓ where
  unit : Op ℓ 0
  ⨂    : Op ℓ 2

data Law (ℓ : Level) : Signature ℓ where
  assoc     : Law ℓ 3
  identity← : Law ℓ 1
  identity→ : Law ℓ 1


open Theory

monoid : (o ℓ : Level) → Theory o ℓ
signature   (monoid o ℓ) = Op o
laws        (monoid o ℓ) = Law ℓ
laws-interp (monoid o ℓ) =
  λ { assoc
      → term ⨂ (term ⨂ (var (# 0) ∷ var (# 1) ∷ nil) ∷ var (# 2) ∷ nil)
      , term ⨂ (var (# 0) ∷ term ⨂ (var (# 0) ∷ var (# 2) ∷ nil) ∷ nil)
    ; identity←
      → term ⨂ (term unit nil ∷ var fzero ∷ nil)
      , var (# 0)
    ; identity→
      → term ⨂ (var (# 0) ∷ term unit nil ∷ nil)
      , var (# 0) }

-- laws : Law 3 → Term Op 3
-- laws assoc = term ⨂ (term ⨂ (var (# 0) ∷ var (# 1) ∷ nil) ∷ var (# 2) ∷ nil)
