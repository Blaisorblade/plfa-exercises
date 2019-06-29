module Nat where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ


infixl 6  _+_  _∸_
infixl 7  _*_

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n  =  zero
suc m * n  =  n + (m * n)

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}


_^_ : ℕ -> ℕ -> ℕ
n ^ zero = 1
n ^ suc k = n * (n ^ k)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

-- write out seven in long form
ex1 : ℕ
ex1 = suc (suc (suc (suc (suc (suc (suc zero))))))

-- compute 3 + 4 showing your reasoning
ex2 : 3 + 4 ≡ 7
ex2 =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨ etc ⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    7
  ∎
  where
  etc : _
  etc = refl

-- Compute 3 * 4, writing out your reasoning as a chain of equations.
ex3 : 3 * 4 ≡ 12
ex3 =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨ etc ⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    12
  ∎
  where
  etc : _
  etc = refl

-- Define exponentiation.
-- Check that 3 ^ 4 is 81.
ex4 : 3 ^ 4 ≡ 81
ex4 =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨ etc ⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    81
  ∎
  where
  etc : _
  etc = refl

-- Compute 5 ∸ 3 and 3 ∸ 5
ex5 : 5 ∸ 3 ≡ 2
ex5 = refl

ex6 : 3 ∸ 5 ≡ 0
ex6 = refl


27+48 : 27 + 48 ≡ 75
27+48 =
  begin
    27 + 48
  ≡⟨⟩
    suc (26 + 48)
  ≡⟨⟩
    suc (suc (25 + 48))
  ≡⟨ etc ⟩
    suc (suc (suc (suc (suc
     (suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc 
         (suc (suc (suc (suc (suc
           (suc (suc (suc (suc (suc
             (suc (suc (0 + 48)))))))))))))))))))))))))))
  ≡⟨⟩
    75
  ∎
  where
  etc : _
  etc = refl



  
