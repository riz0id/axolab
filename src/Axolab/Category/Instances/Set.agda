
module Axolab.Category.Instances.Set where

open import Axolab.Category
open import Axolab.Category.Object.Terminal
open import Axolab.Category.Structure.Cartesian
open import Axolab.Data.Product
open import Axolab.Data.Top
open import Axolab.Prelude

open Category
open Cartesian

-- ---------------------------------------------------------------------------------------------------------------------

Set : (o : Level) → Category (lsuc o) o
Ob     (Set o)       = Setoid o
Hom    (Set o) A B   = A → B
id     (Set o) A     = A
_∘_    (Set o) g f A = g (f A)
id←    (Set o)       = refl
id→    (Set o)       = refl
assoc← (Set o)       = refl
assoc→ (Set o)       = refl

SetTerminal : {o : Level} → Terminal (Set o)
Terminal.⊤        SetTerminal = Top
Terminal.terminal SetTerminal = contract (λ _ → tt) (λ _ → refl)

SetProducts : {o : Level} → Cartesian (Set o)
_×₀_       SetProducts = _×_
_×₁_       SetProducts = λ f g x → f x , g x
π₁         SetProducts = fst
π₂         SetProducts = snd
π₁×₁≡id    SetProducts = refl
π₂×₁≡id    SetProducts = refl
×-unique   SetProducts = λ where refl refl → refl
⊤-terminal SetProducts = SetTerminal
