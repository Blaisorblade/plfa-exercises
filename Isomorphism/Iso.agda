module Iso where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; trans)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)


_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f ∘ g = λ x -> f (g x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g


infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

≃-refl : {A : Set} -> A ≃ A
≃-refl = record
           { to = λ z → z
           ; from = λ z → z
           ; from∘to = λ x → refl
           ; to∘from = λ y → refl
           }

≃-trans : {A B C : Set} -> A ≃ B -> B ≃ C -> A ≃ C
≃-trans
  record
  { to = ab
  ; from = ba
  ; from∘to = ba∘ab
  ; to∘from = ab∘ba
   }
  record
  { to = bc
  ; from = cb
  ; from∘to = cb∘bc
  ; to∘from = bc∘cb }
--  rewrite cb∘bc (ab x)
    = record
       { to = bc ∘ ab
       ; from = ba ∘ cb
       ; from∘to  = λ x -> trans (cong ba (cb∘bc (ab x))) (ba∘ab x)
       ; to∘from = λ x -> trans (cong bc (ab∘ba (cb x))) (bc∘cb x)
       }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

-- exercise: Show that every isomorphism implies an embedding.
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

≲-trans : {A B C : Set} -> A ≲ B -> B ≲ C -> A ≲ C
≲-trans
  record
  { to = ab
  ; from = ba
  ; from∘to = ba∘ab
  }
  record
  { to = bc
  ; from = cb
  ; from∘to = cb∘bc
  } = record
        { to = bc ∘ ab
        ; from = ba ∘ cb
        ; from∘to = λ x -> trans (cong ba (cb∘bc (ab x))) (ba∘ab x)
        }

≲-refl : {A : Set} -> A ≲ A 
≲-refl = record {to = λ a -> a; from = λ a -> a; from∘to = λ a → refl}
module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning



-- exercise: Define equivalence of propositions and show that it
-- is an equivalence relation.
record _<=>_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _<=>_ using (to; from)

<=>-eta-rule : {A B : Set} -> (a<=>b : A <=> B) ->
  a<=>b ≡ record {to = to a<=>b; from = from a<=>b}
<=>-eta-rule p = refl


<=>-refl : {A : Set} -> A <=> A
<=>-refl = record { to = λ x -> x ; from = λ x -> x }

<=>-symm : {A B : Set} -> A <=> B -> B <=> A
<=>-symm record { to = f ; from = g } = record { to = g ; from = f }

<=>-trans : {A B C : Set} -> A <=> B -> B <=> C -> A <=> C
<=>-trans
  record { to = ab ; from = ba }
  record { to = bc ; from = cb } =
    record { to = bc ∘ ab ; from = ba ∘ cb }


