
open import Categorical.Category
open import Topos.Core

module Topos.Logic {o ℓ} {C : Category o ℓ} (E : ElementaryTopos C) where

open import Categorical.Morphism C
open import Prelude
open import Prelude.Data.Sigma
open import Prelude.Equality

open ElementaryTopos E

-- ---------------------------------------------------------------------------------------------------------------------

⊥-unique : {A : Ob} → ({B : Ob} → isContr (Hom A B)) → Σ[ f ∈ Hom A ⊥ ] A ≅ ⊥
⊥-unique p = center p , record
  { from = center p
  ; to   = absurd
  ; iso← = sym (paths p _)       ∘p paths p _
  ; iso→ = sym (paths initial _) ∘p paths initial _
  }

module Internal where
  data Type : Setoid o where
    ob  : Ob → Type
    _⟶_ : Type → Type → Type
    ω   : Type

  τ⟦_⟧ : Type → Ob
  τ⟦ ob x  ⟧ = x
  τ⟦ x ⟶ y ⟧ = [ τ⟦ x ⟧ , τ⟦ y ⟧ ]
  τ⟦ ω     ⟧ = Ω

  data Context : Setoid o where
    _,_ : Context → Type → Context
    nil : Context

  Γ⟦_⟧ : Context → Ob
  Γ⟦ x , y ⟧ = Γ⟦ x ⟧ ×₀ τ⟦ y ⟧
  Γ⟦ nil   ⟧ = ⊤

  data Var : Context → Type → Setoid o where
    here  : {τ   : Type} {Γ : Context} → Var (Γ , τ) τ
    there : {τ σ : Type} {Γ : Context} → Var Γ τ → Var (Γ , σ) τ

  var⟦_⟧ : {Γ : Context} {τ : Type} → Var Γ τ → Hom Γ⟦ Γ ⟧ τ⟦ τ ⟧
  var⟦ here    ⟧ = π₂
  var⟦ there v ⟧ = var⟦ v ⟧ ∘ π₁

  data _⊢_ : Context → Type → Setoid o where
    ref  : {Γ : Context} {τ : Type} → Var Γ τ → Γ ⊢ τ
    lam  : {Γ : _} {τ σ : _} → (Γ , τ) ⊢ σ → Γ ⊢ (τ ⟶ σ)
    app  : {Γ : _} {τ σ : _} → Γ ⊢ (τ ⟶ σ) → Γ ⊢ τ → Γ ⊢ σ
    tru  : {Γ : _} → Γ ⊢ ω

    and : {Γ : _} → Γ ⊢ ω → Γ ⊢ ω → Γ ⊢ ω
    all : {Γ : _} {α : _} → Γ ⊢ (α ⟶ ω) → Γ ⊢ ω

    _⊃_  : {Γ : _} → Γ ⊢ ω → Γ ⊢ ω → Γ ⊢ ω
    _≡?_ : {Γ : _} {α : _} → Γ ⊢ α → Γ ⊢ α → Γ ⊢ ω
