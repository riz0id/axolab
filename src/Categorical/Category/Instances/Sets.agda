module Categorical.Category.Instances.Sets where

open import Categorical.Category
open import Categorical.Category.Structure.Cartesian
open import Categorical.Category.Structure.Monoidal
open import Categorical.Object.Terminal
open import Prelude
open import Prelude.Data.Product
open import Prelude.Data.Unit
open import Prelude.Equality

private
  variable
    o : Level

-- ---------------------------------------------------------------------------------------------------------------------

open Category
open Cartesian
open Terminal

Sets : (o : Level) → Category (lsuc o) o
Ob     (Sets o) = Setoid o
Hom    (Sets o) = λ A B → A → B
id     (Sets o) = λ X → X
_∘_    (Sets o) = λ f g x → f (g x)
id←    (Sets o) = λ f → refl
id→    (Sets o) = λ f → refl
assoc← (Sets o) = λ f g h → refl
assoc→ (Sets o) = λ f g h → refl

TerminalSets : Terminal (Sets o)
⊤        TerminalSets = Top
terminal TerminalSets .center A = tt
terminal TerminalSets .paths  f = funExt λ _ → refl

CartesianSets : Cartesian (Sets o)
_×₀_     CartesianSets = _×_
_×₁_     CartesianSets f g = λ x → f x , g x
π₁       CartesianSets = fst
π₂       CartesianSets = snd
π₁×₁≡id  CartesianSets f g = funExt λ _ → refl
π₂×₁≡id  CartesianSets f g = funExt λ _ → refl
×-unique CartesianSets f g h refl refl = funExt λ x → refl
terminal CartesianSets = TerminalSets
