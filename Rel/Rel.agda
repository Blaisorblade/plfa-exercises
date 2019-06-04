module Rel where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; *-zeroʳ)


data _≤_ : ℕ -> ℕ -> Set where
  z≤n : ∀ {n : ℕ} -> zero ≤ n
  s≤s : ∀ {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)


≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)


+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)


+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- exercise : show that multiplication is monotonic with regard to inequality
*-mono-≤ : ∀ (m n p q : ℕ) -> m ≤ n -> p ≤ q -> m * p ≤ n * q
*-mono-≤ .0 n p q z≤n pf2 = z≤n
*-mono-≤ .(suc _) .(suc _) .0 q (s≤s {m} {n} pf1) z≤n rewrite *-zeroʳ m = z≤n
*-mono-≤ .(suc _) .(suc _) .(suc _) .(suc _) (s≤s {m} {n} pf1) (s≤s {p} {q} pf2)
  = s≤s (+-mono-≤ p q (m * suc p) (n * suc q) pf2 (*-mono-≤ m n (suc p) (suc q) pf1 (s≤s pf2)))



infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n



-- exercise : show that strict inequality is transitive.
<-trans : ∀ (m n p : ℕ) -> m < n -> n < p -> m < p
<-trans zero n (suc p) pf1 pf2 = z<s
<-trans (suc m) (suc n) (suc p) (s<s pf1) (s<s pf2) = s<s (<-trans m n p pf1 pf2)

--exercise: Show that strict inequality satisfies a weak version of trichotomy

data Trichotomy (m n : ℕ) : Set where
  less : m < n -> Trichotomy m n
  equal : m ≡ n -> Trichotomy m n
  greater : n < m -> Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) -> Trichotomy m n
<-trichotomy zero zero = equal refl
<-trichotomy zero (suc n) = less z<s
<-trichotomy (suc m) zero = greater z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
<-trichotomy (suc m) (suc n) | less x = less (s<s x)
<-trichotomy (suc m) (suc n) | equal x = equal (cong suc x)
<-trichotomy (suc m) (suc n) | greater x = greater (s<s x)
 
-- exercise: Show that addition is monotonic with respect to strict inequality
<-suc : ∀ (n : ℕ) -> n < suc n
<-suc zero = z<s
<-suc (suc n) = s<s (<-suc n)

+-mono-<-R : ∀ (m p q : ℕ) -> p < q -> m + p < m + q
+-mono-<-R zero p q pf1 = pf1
+-mono-<-R (suc m) p q pf1 = s<s (+-mono-<-R m p q pf1)


+-mono-<-L : ∀ (m n q : ℕ) -> m < n -> m + q < n + q
+-mono-<-L m n q pf rewrite +-comm m q | +-comm n q = +-mono-<-R q m n pf

  
+-mono-< : ∀ (m n p q : ℕ) -> m < n -> p < q -> m + p < n + q
+-mono-< m n p q <mn <pq = <-trans (m + p) (n + p) (n + q) (+-mono-<-L m n p <mn) (+-mono-<-R n p q <pq)


--exercise: Show that suc m ≤ n implies m < n, and conversely.
≤-iff-<-1 : ∀ (m n : ℕ) -> suc m ≤ n -> m < n
≤-iff-<-1 zero (suc n) pf = z<s
≤-iff-<-1 (suc m) (suc n) (s≤s pf) = s<s (≤-iff-<-1 m n pf)


≤-iff-<-2 : ∀ (m n : ℕ) -> m < n -> suc m ≤ n
≤-iff-<-2 zero (suc n) pf = s≤s z≤n
≤-iff-<-2 (suc m) (suc n) (s<s pf) = s≤s (≤-iff-<-2 m n pf)

≤-succ : ∀ (n : ℕ) -> n ≤ (suc n)
≤-succ zero = z≤n
≤-succ (suc n) = s≤s (≤-succ n)

-- exercise : Give an alternative proof that strict inequality is transitive,
-- using the relation between strict inequality and inequality and the fact
-- that inequality is transitive.
<-trans-revisited : ∀ (m n p) -> m < n -> n < p -> m < p
<-trans-revisited m n p <-mn <-np with ≤-iff-<-2 m n <-mn | ≤-iff-<-2 n p <-np
...                                  | ≤p                 | ≤q
  with   (≤-trans ≤p (≤-succ n))
...    | pf1
  with   (≤-trans pf1 ≤q)
...    | pf2                          = ≤-iff-<-1 m p pf2
