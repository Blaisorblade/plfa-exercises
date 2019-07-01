module Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Iso using (_≃_; _≲_; extensionality; _<=>_; <=>-eta-rule; ≃-trans)
open Iso.≃-Reasoning
open _<=>_ using (to; from)
open _≃_ using (to; from; to∘from; from∘to)


data _x_ (A B : Set) : Set where
  ⟨_,_⟩ : A -> B -> (A x B)

proj₁ : {A B : Set} -> A x B -> A
proj₁ ⟨ a , b ⟩ = a

proj₂ : {A B : Set} -> A x B -> B
proj₂ ⟨ a , b ⟩ = b

X-eta-rule : {A B : Set} -> (p : A x B) -> p ≡ ⟨ proj₁ p , proj₂ p ⟩
X-eta-rule ⟨ a , b ⟩ = refl

infixr 2 _x_

--exercise : Show that A <=> B is isomorphic to (A -> B) x (B -> A)

<=>-iso : {A B : Set} -> A <=> B ≃ (A -> B) x (B -> A)
<=>-iso =
  record
  { to = λ a<=>b -> ⟨ _<=>_.to a<=>b , _<=>_.from a<=>b ⟩
  ; from = λ p -> record { to = proj₁ p ; from = proj₂ p }
  ; from∘to = λ a<=>b -> <=>-eta-rule a<=>b
  ; to∘from = λ p -> sym (X-eta-rule p)
  }


data _⊎_ (A B : Set) : Set where
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

-- exercise: Show sum is commutative up to isomorphism.

⊎-comm : ∀ {A B : Set} -> A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
  { to = flip
  ; from = flip
  ; from∘to = flip-idem
  ; to∘from = flip-idem }
  where
  flip : ∀ {X Y} -> X ⊎ Y -> Y ⊎ X
  flip (inj₁ x) = inj₂ x
  flip (inj₂ y) = inj₁ y

  flip-idem : ∀ {X Y : Set} (xy : X ⊎ Y) -> flip (flip xy) ≡ xy
  flip-idem (inj₁ x) = refl
  flip-idem (inj₂ y) = refl


-- exercise: Show sum is associative up to isomorphism

⊎-assoc : ∀ {A B C : Set} -> A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc =
  record
  { to = left-assoc
  ; from = right-assoc
  ; from∘to = right-left-≡
  ; to∘from = left-right-≡ }
  where
  left-assoc : ∀ {A B C : Set} -> A ⊎ (B ⊎ C) -> (A ⊎ B) ⊎ C
  left-assoc (inj₁ a) = inj₁ (inj₁ a)
  left-assoc (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
  left-assoc (inj₂ (inj₂ c)) = inj₂ c

  right-assoc : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C -> A ⊎ (B ⊎ C)
  right-assoc (inj₁ (inj₁ a)) = inj₁ a
  right-assoc (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
  right-assoc (inj₂ c) = inj₂ (inj₂ c)

  right-left-≡
    : ∀ {A B C : Set} (a[bc] : A ⊎ (B ⊎ C))
    -> right-assoc (left-assoc a[bc]) ≡ a[bc]
  right-left-≡ (inj₁ a) = refl
  right-left-≡ (inj₂ (inj₁ b)) = refl
  right-left-≡ (inj₂ (inj₂ c)) = refl

  left-right-≡
      : ∀ {A B C : Set} ([ab]c : (A ⊎ B) ⊎ C)
    -> left-assoc (right-assoc [ab]c) ≡ [ab]c
  left-right-≡ (inj₁ (inj₁ a)) = refl
  left-right-≡ (inj₁ (inj₂ b)) = refl
  left-right-≡ (inj₂ c) = refl
  
  

data ⊥ : Set where

-- exercise: Show empty is the left identity of sums up to isomorphism.

⊥-identityʳ : ∀ {A : Set} -> A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
  { to = l
  ; from = r
  ; from∘to = r∘l
  ; to∘from = l∘r }
  where
  l : ∀ {A : Set} -> A ⊎ ⊥ -> A
  l (inj₁ a) = a

  r : ∀ {A : Set} -> A -> A ⊎ ⊥
  r = inj₁

  r∘l : ∀ {A : Set} (a-⊥ : A ⊎ ⊥) -> r (l a-⊥) ≡ a-⊥ 
  r∘l (inj₁ a) = refl

  l∘r : ∀ {A : Set} (a : A) -> l (r a) ≡ a
  l∘r a = refl


-- with copatterns!
⊥-identityʳ-co-patterns : ∀ {A : Set} -> A ⊎ ⊥ ≃ A
to ⊥-identityʳ-co-patterns (inj₁ a) = a
from ⊥-identityʳ-co-patterns = inj₁
from∘to ⊥-identityʳ-co-patterns (inj₁ a) = refl
to∘from ⊥-identityʳ-co-patterns _ = refl


⊥-identityˡ  : ∀ {A : Set} -> ⊥ ⊎ A ≃ A
⊥-identityˡ = ≃-trans ⊎-comm ⊥-identityʳ

-- exercise: show the weak distributive law holds
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) x C → A ⊎ (B x C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

-- exercise: show that a disjunct of conjuncts implies a conjunct of disjuncts
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A x B) ⊎ (C x D) → (A ⊎ C) x (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

