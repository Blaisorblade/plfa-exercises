module Classical where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to ⊎-case)
open import Data.Product using (_×_; _,_)
open import Iso using (_≃_; extensionality)
open import Rel using (_<_; z<s; s<s)
open import Negation using (¬_)

excluded-middle : ∀ (A : Set) -> Set
excluded-middle A = A ⊎ ¬ A

double-negation-elim : ∀ (A : Set) -> Set
double-negation-elim A = ¬ ¬ A -> A

pierce's-law : ∀ (A B : Set) -> Set
pierce's-law A B = ((A -> B) -> A) -> A 
  
implication-as-disjunction : ∀ (A B : Set) -> Set
implication-as-disjunction A B = (A -> B) -> ¬ A ⊎ B


de-morgan : ∀ (A B : Set) -> Set
de-morgan A B = ¬ (¬ A × ¬ B) -> A ⊎ B

EM=>DNE : (∀ (A : Set) ->  excluded-middle A) -> (∀ (A' : Set) -> double-negation-elim A')
EM=>DNE em A' ¬¬a with (em A')
EM=>DNE em A' ¬¬a | inj₁ a'  = a'
EM=>DNE em A' ¬¬a | inj₂ ¬a' = ⊥-elim (¬¬a ¬a')

EM=>PL : (∀ (A : Set) -> excluded-middle A) -> (∀ (A B : Set) -> pierce's-law A B)
EM=>PL em A B [ab]a with (em B)
EM=>PL em A B [ab]a | inj₁ b  = [ab]a λ _ -> b
EM=>PL em A B [ab]a | inj₂ ¬b with (em A)
EM=>PL em A B [ab]a | inj₂ ¬b | inj₁ a  = a
EM=>PL em A B [ab]a | inj₂ ¬b | inj₂ ¬a = [ab]a λ a -> ⊥-elim (¬a a)
