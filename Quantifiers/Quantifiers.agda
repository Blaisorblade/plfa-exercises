module Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Iso using (_≃_)

∀-elim : ∀ {A : Set} (B : A → Set)
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim B L M = L M


-- exercise: Show that universals distribute over conjunction
∀-distrib-×
  :   ∀ {A : Set} {B C : A -> Set}
  -> (∀ (a : A) → B a × C a) ≃ (∀ (a : A) → B a) × (∀ (a : A) → C a)
∀-distrib-× {A} {B} {C} =
  record
  { to = λ a->b×c ->
             let a->b : (a : A) -> B a
                 a->b a = proj₁ (a->b×c a)
                 a->c : (a : A) -> C a
                 a->c a = proj₂ (a->b×c a)
             in a->b , a->c 
  ; from = λ [a->b]×[a->c] -> λ a ->
               let a->b : (a : A) -> B a
                   a->b = proj₁ [a->b]×[a->c]
                   a->c : (a : A) -> C a
                   a->c = proj₂ [a->b]×[a->c]
               in (a->b a) , (a->c a)
  ; from∘to = λ a->[b×c] -> refl
  ; to∘from = λ [a->b]×[a->c] -> refl }



⊎∀-implies-∀⊎
  :  ∀ {A : Set} {B C : A -> Set} ->
    (∀ (x : A) -> B x) ⊎ (∀ (x : A) -> C x)  →  ∀ (x : A) -> B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ a->b) = λ a -> inj₁ (a->b a)
⊎∀-implies-∀⊎ (inj₂ a->c) = λ a -> inj₂ (a->c a)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri


-- exercise : Let B be a type indexed by Tri, that is B : Tri → Set.
-- Show that ∀ (x : Tri) → B x is isomorphic to B aa × B bb × B cc.


postulate
  extensionality : {A : Set} {B : A → Set}
    {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

∀-× : ∀ {B : Tri -> Set}
   -> (∀ (t : Tri) -> B t) ≃ B aa × B bb × B cc
∀-× =
  record
  { to = λ b[t] ->
           (b[t] aa) , ((b[t] bb) , (b[t] cc))
  ; from = f
  ; from∘to =  lemma 
  ; to∘from = λ a×b×c -> refl }
  where
   f : ∀ {B : Tri -> Set}
     -> (B aa × B bb × B cc) -> (∀ (t : Tri) -> B t)
   f a×b×c aa = proj₁ a×b×c
   f a×b×c bb = proj₁ (proj₂ a×b×c)
   f a×b×c cc = proj₂ (proj₂ a×b×c)  
   
   lemma : ∀ {B : Tri -> Set} -> 
        (b[t] : (t : Tri) → B t) → f (b[t] aa , b[t] bb , b[t] cc) ≡ b[t]
   lemma b[t] = extensionality λ{ aa -> refl
                                ; bb -> refl
                                ; cc -> refl}

  
