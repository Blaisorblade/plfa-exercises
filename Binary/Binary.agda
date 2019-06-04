module Binary where

import Data.Nat as Nat
open Nat using (ℕ; _*_; _+_; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; inspect; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
import Data.Bool as Bool
open Bool using (Bool; false; true)
import Data.Product as Prod
open Prod using (_×_; _,_)
import Data.List as List
open List using ([]; _∷_)
open import Ind using (+-identity; +-succ)
import Rel
open import Rel using (_<_; z<s)

data Bin : Set where
  nil : Bin
  x0_ : Bin -> Bin
  x1_ : Bin -> Bin
    

inc : Bin -> Bin
inc nil    = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

to-nat : Bin -> ℕ
to-nat nil = 0
to-nat (x0 b) = (to-nat b) + (to-nat b)
to-nat (x1 b) = suc ((to-nat b) + (to-nat b))

from-nat : ℕ -> Bin
from-nat zero = x0 nil
from-nat (suc n) = inc (from-nat n)

has-x1 : Bin -> Bool
has-x1 nil = false
has-x1 (x0 x) = has-x1 x
has-x1 (x1 x) = true

normalise : Bin -> Bin
normalise nil = nil
normalise (x1 x) = x1 (normalise x)
normalise (x0 x) with (has-x1 x)
normalise (x0 x) | false = nil
normalise (x0 x) | true = x0 (normalise x)


data One : Bin -> Set where
  is-one : One (x1 nil)
  x0-there : ∀ {b : Bin} -> One b -> One (x0 b)
  x1-there : ∀ {b : Bin} -> One b -> One (x1 b)

data Can : Bin -> Set where
  zero : Can (x0 nil)
  leading-x1 : ∀ {b : Bin} -> One b -> Can  b


inc-one : ∀ {b : Bin} -> One b -> One (inc b)
inc-one is-one = x0-there is-one
inc-one (x0-there p) = x1-there p
inc-one (x1-there p) = x0-there (inc-one p)

inc-can : ∀ {b : Bin} -> Can b -> Can (inc b)
inc-can zero = leading-x1 is-one
inc-can (leading-x1 x) = leading-x1 (inc-one x)


can-to-nat : ∀ {n : ℕ} -> Can (from-nat n)
can-to-nat {zero} = zero
can-to-nat {suc n} = inc-can (can-to-nat {n})

to-suc-inc : ∀ (b : Bin) -> to-nat (inc b) ≡ suc (to-nat b)
to-suc-inc nil = refl
to-suc-inc (x0 b) = refl
to-suc-inc (x1 b) rewrite (to-suc-inc b) | +-succ (to-nat b) (to-nat b) = refl

to-from : ∀ {n : ℕ} -> to-nat (from-nat n) ≡ n
to-from {zero} = refl
to-from {suc n} rewrite to-suc-inc (from-nat n) | to-from {n} = refl

pos-double : ∀ (n : ℕ) -> 0 < n -> 0 < n + n
pos-double (suc n) p = z<s

one-pos : ∀ (b : Bin) -> One b -> 0 < (to-nat b)
one-pos .(x1 nil) is-one = z<s
one-pos .(x0 _) (x0-there {b} p) with one-pos b p
...                                  | pf  = pos-double (to-nat b) pf
one-pos .(x1 _) (x1-there {b} p) = z<s



suc-lem : ∀ (n : ℕ) -> n + suc (suc n) ≡ suc n + suc n
suc-lem zero = refl
suc-lem (suc n) rewrite +-succ n (suc (suc n)) = refl

doubling-nat : ∀ (n : ℕ) -> 0 < n -> from-nat (n + n) ≡ x0 (from-nat n)
doubling-nat .1 (z<s {zero}) = refl
doubling-nat .(suc (suc n)) (z<s {suc n})
  rewrite suc-lem n
         | doubling-nat (suc n) (z<s {n}) = refl

x0-double : ∀ (b : Bin) -> One b -> from-nat (to-nat b + to-nat b) ≡ x0 b
one-from-to : ∀ {b : Bin} -> One b -> from-nat (to-nat b) ≡ b

x0-double b p rewrite (one-from-to {b} p)
                     | doubling-nat (to-nat b) (one-pos b p)
                     | (one-from-to {b} p) = refl
one-from-to is-one = refl
one-from-to {b} (x0-there {b1} pf) rewrite x0-double b1 pf = refl
one-from-to {b} (x1-there {b1} pf) rewrite x0-double b1 pf = refl
  

can-iso : ∀ {b : Bin} -> Can b -> from-nat (to-nat b) ≡ b
can-iso zero = refl
can-iso (leading-x1 p) = one-from-to p


--- """unit tests""" ---
0B = x0 nil
1B = x1 nil
2B = x0 x1 nil
3B = x1 x1 nil
4B = x0 x0 x1 nil

_ : to-nat 0B ≡ 0
_ = refl

_ : to-nat 1B ≡ 1
_ = refl

_ : to-nat 2B ≡ 2
_ = refl

_ : to-nat 3B ≡ 3
_ = refl

_ : to-nat 4B ≡ 4
_ = refl

------------------------

