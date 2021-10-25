
open import Prelude

module Relation.Structure.Proset {o} (U : Setoid o) where

open import Prelude.Equality

private
  variable
    A B C D : U

-- ---------------------------------------------------------------------------------------------------------------------

record Proset (ℓ ℓ' : Level) : Setoid (lsuc (o ⊔ ℓ ⊔ ℓ')) where
  infix 4 _≤_
  field
    _≤_ : U → U → Setoid ℓ

  field
    reflexive≤ : A ≡ B → A ≤ B
    trans≤     : A ≤ B → B ≤ C → A ≤ C
    prop≤      : (p q : A ≤ B) → p ≡ q

  refl≤ : A ≤ A
  refl≤ = reflexive≤ refl

  resp≤←≈ : {A' : U} → A ≡ A' → A ≤ B → A' ≤ B
  resp≤←≈ A≈A' A≤B = trans≤ (reflexive≤ (sym A≈A')) A≤B

  resp≤→≈ : {B' : U} → B ≡ B' → A ≤ B → A ≤ B'
  resp≤→≈ B≈B' A≤B = trans≤ A≤B (reflexive≤ B≈B')

  const≤← : (p : A ≤ B) → trans≤ p refl≤ ≡ p
  const≤← p = prop≤ (trans≤ p refl≤) p

  const≤→ : (p : A ≤ B) → trans≤ refl≤ p ≡ p
  const≤→ p = prop≤ (trans≤ refl≤ p) p

  assoc≤← : (p : A ≤ B) → (q : B ≤ C) → (s : C ≤ D) → trans≤ (trans≤ p q) s ≡ trans≤ p (trans≤ q s)
  assoc≤← p q s = prop≤ (trans≤ (trans≤ p q) s) (trans≤ p (trans≤ q s))

  assoc≤→ : (p : A ≤ B) → (q : B ≤ C) → (s : C ≤ D) → trans≤ p (trans≤ q s) ≡ trans≤ (trans≤ p q) s
  assoc≤→ p q s = prop≤ (trans≤ p (trans≤ q s)) (trans≤ (trans≤ p q) s)
