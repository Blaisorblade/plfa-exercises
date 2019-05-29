module Nat where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n  =  zero
suc m * n  =  n + (m * n)

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
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    7
  ∎

ex3 : 3 * 4 ≡ 12
ex3 = refl

ex4 : 3 ^ 4 ≡ 81
ex4 = refl

ex5 : 5 ∸ 3 ≡ 2
ex5 = refl

ex6 : 3 ∸ 5 ≡ 0
ex6 = refl
