module Iso where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)


_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f ∘ g = λ x -> f (g x)

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

≃-implies-≲ : ∀ {A B : Set} -> A ≃ B -> A ≲ B
≃-implies-≲
  record
    { to = f
    ; from = f-inv
    ; from∘to = f-inv∘f 
    ; to∘from = f∘f-inv
    } = record { to = f
               ; from = f-inv
               ; from∘to = f-inv∘f
               }

-- exercise: Define equivalence of propositions and show that it
-- is an equivalence relation.
record _<=>_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

<=>-refl : {A : Set} -> A <=> A
<=>-refl = record { to = λ x -> x ; from = λ x -> x }

<=>-symm : {A B : Set} -> A <=> B -> B <=> A
<=>-symm record { to = f ; from = g } = record { to = g ; from = f }

<=>-trans : {A B C : Set} -> A <=> B -> B <=> C -> A <=> C
<=>-trans
  record { to = ab ; from = ba }
  record { to = bc ; from = cb } =
    record { to = bc ∘ ab ; from = ba ∘ cb }
