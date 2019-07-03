module Stable where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap) renaming ([_,_] to ⊎-case)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Iso using (_≃_; extensionality)
open _≃_ using (to; from)
open import Rel using (_<_; z<s; s<s)
open import Negation using (¬_; ⊎-dual-×; ¬¬-intro)

-- exercise: Show that any negated formula is stable, and that the conjunction of two stable formulas is stable.
  
Stable : Set -> Set
Stable A = ¬ ¬ A -> A


¬-map : ∀ {A B : Set} -> (A -> B) -> (¬ B -> ¬ A)
¬-map a->b ¬b = λ a -> ¬b (a->b a)


¬¬-map : ∀ {A B : Set} -> (A -> B) -> (¬ ¬ A -> ¬ ¬ B)
¬¬-map a->b ¬¬a = λ ¬b -> ¬¬a (¬-map a->b ¬b) 


neg-stable : ∀ {A : Set} -> Stable (¬ A)
neg-stable ¬¬¬a = λ a -> ¬¬¬a (¬¬-intro a)


conj-stable : ∀ {A B : Set} -> Stable A -> Stable B -> Stable (A × B)
conj-stable {A} {B} dne-A dne-B ¬¬[a×b] =
  let ¬¬a : ¬ ¬ A
      ¬¬a = ¬¬-map proj₁ ¬¬[a×b]
      ¬¬b : ¬ ¬ B
      ¬¬b = ¬¬-map proj₂ ¬¬[a×b]
      a   : A
      a   = dne-A ¬¬a
      b   : B
      b   = dne-B ¬¬b
  in a , b
