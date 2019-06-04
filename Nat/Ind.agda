module Ind where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)


+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl


+-identity : ∀ (n : ℕ) -> n + 0 ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-succ : ∀ (m n : ℕ) -> (m + suc n) ≡ suc (m + n)
+-succ zero n = refl
+-succ (suc m) n rewrite +-succ m n = refl

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm zero n = sym (+-identity n)
+-comm (suc m) n rewrite +-succ n m | +-comm m n = refl

-- exercise: Show
--           m + (n + p) ≡ n + (m + p)

+-swap : ∀ (m n p : ℕ) -> m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

 
-- exercise: Show multiplication distributes over addition, that is,
--           (m + n) * p ≡ m * p + n * p
*-distrib-+ : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl



-- exercise: Show multiplication is associative
*-assoc : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

-- exercise: Show multiplication is commutative

---------------- lemmas ------------
*-zero : ∀ (n : ℕ) -> zero ≡ n * zero
*-zero zero = refl
*-zero (suc n) = *-zero n

*-one : ∀ (n : ℕ) -> n * 1 ≡ n
*-one zero = refl
*-one (suc n)  rewrite *-one n = refl

*-succ : ∀ ( m n : ℕ) -> m * suc n ≡ m + m * n
*-succ zero n = refl
*-succ (suc m) n rewrite *-succ m n | +-swap n m (m * n) = refl
------------------------------------

*-comm : ∀ (m n : ℕ) -> (m * n) ≡ (n * m)
*-comm zero n = *-zero n
*-comm (suc m) n rewrite *-succ n m | *-comm m n = refl

-- exercise : Show
--           zero ∸ n ≡ zero
0∸n≡0 : ∀ (n : ℕ) -> 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl


-- exercise: Show that monus associates with addition, that is,
-- m ∸ n ∸ p ≡ m ∸ (n + p)
zero-∸ : ∀ (n : ℕ) -> zero ∸ n ≡ zero
zero-∸ zero = refl
zero-∸ (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) -> m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero zero = refl
∸-+-assoc m (suc n) zero rewrite +-identity n = refl
∸-+-assoc m zero (suc p) = refl
∸-+-assoc zero (suc n) (suc p) = refl
∸-+-assoc (suc m) (suc n) (suc p) =  ∸-+-assoc m n (suc p)




