module Binary where

import Data.Nat as Nat
open Nat using (ℕ; _*_; _+_; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; inspect)
import Data.Bool as Bool
open Bool using (Bool; false; true)
import Data.Product as Prod
open Prod using (_×_; _,_)
import Data.List as List
open List using ([]; _∷_)


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
to-nat (x0 b) = 2 * (to-nat b)
to-nat (x1 b) = 1 + (2 * (to-nat b))

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

