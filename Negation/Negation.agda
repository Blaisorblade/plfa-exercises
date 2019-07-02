module Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to ⊎-case)
open import Data.Product using (_×_; _,_)
open import Iso using (_≃_; extensionality)
open import Rel using (_<_; z<s; s<s)

¬_ : Set -> Set
¬ A = A -> ⊥

infix 3 ¬_

¬-elim : ∀ {A : Set} -> ¬ A -> A -> ⊥
¬-elim ¬a a = ¬a a

¬¬-intro : ∀ {A : Set} -> A -> ¬ ¬ A
¬¬-intro a = λ ¬a → ¬a a

_≢_ : ∀ {A : Set} -> A -> A -> Set
x ≢ y = ¬ (x ≡ y)

--exercise Show that strict inequality is irreflexive, that is, n < n holds for no n.

<-irreflexive : ∀ {n : ℕ} -> ¬ (n < n)
<-irreflexive (s<s p) = <-irreflexive p


-- exercise: Show that strict inequality satisfies trichotomy,

data Trichotomy (m n : ℕ) : Set where
  lesser : m < n -> ¬ (m ≡ n) -> ¬ (n < m) -> Trichotomy m n
  equal : ¬ (m < n) -> m ≡ n -> ¬ (n < m) -> Trichotomy m n
  greater : ¬ (m < n) -> ¬ (m ≡ n) -> (n < m) -> Trichotomy m n

pred-≡ : ∀ {m n : ℕ} -> suc m ≡ suc n -> m ≡ n
pred-≡ refl = refl

suc-≡ : ∀ {m n : ℕ} -> m ≡ n -> suc m ≡ suc n
suc-≡ refl = refl

pred-< : ∀ {m n : ℕ} -> suc m < suc n -> m < n
pred-< (s<s p) = p

assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality (λ x → ⊥-elim (¬x x))


suc-trichotomy : ∀ {m n : ℕ} -> Trichotomy m n -> Trichotomy (suc m) (suc n)
suc-trichotomy (lesser l ¬e ¬g)
  = lesser (s<s l) (λ p -> ¬e (pred-≡ p)) (λ p -> ¬g (pred-< p))
suc-trichotomy (equal ¬l e ¬g)
  = equal (λ p -> ¬l (pred-< p)) (suc-≡ e) (λ p -> ¬g (pred-< p))
suc-trichotomy (greater ¬l ¬e g)
  = greater (λ p -> ¬l (pred-< p)) (λ p -> ¬e (pred-≡ p) ) (s<s g)


<-trichotomy : ∀ (m n : ℕ) -> Trichotomy m n
<-trichotomy zero zero = equal (λ ()) refl (λ ())
<-trichotomy zero (suc n) = lesser z<s (λ ()) (λ ())
<-trichotomy (suc m) zero = greater (λ ()) (λ ()) z<s
<-trichotomy (suc m) (suc n) = suc-trichotomy (<-trichotomy m n)

-- exercise: Show that conjunction, disjunction, and negation are related by a version of De Morgan’s Law.
⊎-dual-× : ∀ {A B : Set} -> ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
  { to  = t
  ; from = f
  ; from∘to = λ ¬a+b -> assimilation (f (t (¬a+b))) ¬a+b
  ; to∘from = t∘f }
  where
  t : ∀ {A B : Set} -> ¬ (A ⊎ B) ->  (¬ A) × (¬ B)
  t = λ ¬a+b -> (λ a -> ¬a+b (inj₁ a)) , λ b -> ¬a+b (inj₂ b)

  f : ∀ {A B : Set} -> (¬ A) × (¬ B) -> ¬ (A ⊎ B)
  f (¬a , ¬b) = ⊎-case ¬a ¬b

  t∘f :  ∀ {A B : Set} -> (¬a×¬b : ¬ A × ¬ B) -> t (f (¬a×¬b)) ≡ ¬a×¬b
  t∘f (¬a , ¬b) = refl


