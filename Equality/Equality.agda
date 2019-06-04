module Equality where

import Rel
open Rel using (_≤_; s≤s; ≤-trans; ≤-refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
import Ind
open import Ind using (+-comm)

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} -> {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : ∀ {A : Set} -> {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl
  
cong : ∀ {A B : Set} -> (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} {x y : A} {u v : B} (f : A -> B -> C)
   -> x ≡ y -> u ≡ v -> f x u ≡ f y v
cong₂ f refl refl = refl

pointwise-eq : ∀ {A B : Set} {f g : A -> B} -> f ≡ g -> ∀ (x : A) -> f x ≡ g x
pointwise-eq refl x = refl


subst : ∀ {A : Set} {x y : A} -> (P : A -> Set) -> x ≡ y -> P x -> P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl



-- exercise :
-- Define a module ≤-Reasoning and use it to rewrite a proof that addition is monotonic
module ≤-Reasoning where
  open Rel using (_≤_; ≤-trans; ≤-refl)
  

  infix  1 begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  begin x≤y  =  x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y  =  x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z  =  ≤-trans x≤y y≤z

  _∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  x ∎  =  ≤-refl

open ≤-Reasoning


+-mono-l-≤ : ∀ {m n p : ℕ} -> m ≤ n -> m + p ≤ n + p
+-mono-r-≤ : ∀ {n p q : ℕ} -> p ≤ q -> n + p ≤ n + q
+-mono-≤ : ∀ {m n p q : ℕ} -> m ≤ n -> p ≤ q -> m + p ≤ n + q

+-mono-r-≤ {zero} p≤q = p≤q
+-mono-r-≤ {suc n} {p} {q} p≤q =
  begin
    suc (n + p)
  ≤⟨ (s≤s (+-mono-r-≤ {n} {p} {q} p≤q)) ⟩
    suc (n + q)
  ∎

+-mono-l-≤ {m} {n} {p} m≤n rewrite +-comm m p | +-comm n p = +-mono-r-≤ {p} {m} {n} m≤n
+-mono-≤ {m} {n} {p} {q} m≤n p≤q =
  begin
    m + p
  ≤⟨ +-mono-l-≤ m≤n ⟩
    n + p
  ≤⟨ +-mono-r-≤ p≤q ⟩
    n + q
  ∎

