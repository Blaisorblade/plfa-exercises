module Classical where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap) renaming ([_,_] to ⊎-case)
open import Data.Product using (_×_; _,_)
open import Iso using (_≃_; extensionality)
open _≃_ using (to; from)
open import Rel using (_<_; z<s; s<s)
open import Negation using (¬_; ⊎-dual-×)

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

-- How we prove equivalence
-- EM <=> DNE
-- EM  => PL
-- PL  => DNE
-- EM  <=> IAD
-- EM  <=> DM


EM=>DNE : (∀ (A : Set) ->  excluded-middle A)
       -> (∀ (A' : Set) -> double-negation-elim A')
EM=>DNE em A' ¬¬a with (em A')
EM=>DNE em A' ¬¬a | inj₁ a'  = a'
EM=>DNE em A' ¬¬a | inj₂ ¬a' = ⊥-elim (¬¬a ¬a')

DNE=>EM : (∀ (A : Set) ->  double-negation-elim A)
       -> (∀ (B : Set) -> excluded-middle B)
DNE=>EM dne B = dne (B ⊎ ¬ B) (lemma B)
  where
  lemma : ∀ (B : Set) -> ¬ (¬ (B ⊎ ¬ B))
  lemma B b+¬b with ((to ⊎-dual-×) b+¬b)
  lemma B b+¬b | (¬b , ¬¬b) = ¬¬b ¬b

EM=>PL : (∀ (A : Set) -> excluded-middle A)
      -> (∀ (A B : Set) -> pierce's-law A B)
EM=>PL em A B [ab]a with (em B)
EM=>PL em A B [ab]a | inj₁ b  = [ab]a λ _ -> b
EM=>PL em A B [ab]a | inj₂ ¬b with (em A)
EM=>PL em A B [ab]a | inj₂ ¬b | inj₁ a  = a
EM=>PL em A B [ab]a | inj₂ ¬b | inj₂ ¬a = [ab]a λ a -> ⊥-elim (¬a a)

PL=>DNE : (∀ (A B : Set) -> pierce's-law A B)
      -> (∀ (C : Set) -> double-negation-elim C)
PL=>DNE pl C = lemma C (pl C ⊥)
  where
  lemma : ∀ (A : Set) -> ((¬ A -> A) -> A) -> (¬ ¬ A -> A)
  lemma A [¬a->a]->a ¬¬a = [¬a->a]->a λ ¬a -> ⊥-elim (¬¬a ¬a)

EM=>IAD : (∀ (A : Set) -> excluded-middle A)
       -> (∀ (B C : Set) -> implication-as-disjunction B C)
EM=>IAD em B C b->c with (em B) 
EM=>IAD em B C b->c | inj₁ b = inj₂ (b->c b)
EM=>IAD em B C b->c | inj₂ ¬b = inj₁ ¬b


EM=>DM : (∀ (A : Set) -> excluded-middle A)
      -> (∀ (B C : Set) -> de-morgan B C)
EM=>DM em B C ¬[¬b×¬c] with (em B) 
EM=>DM em B C ¬[¬b×¬c] | inj₁ b = inj₁ b
EM=>DM em B C ¬[¬b×¬c] | inj₂ ¬b with (em C)
EM=>DM em B C ¬[¬b×¬c] | inj₂ ¬b | inj₁ c  = inj₂ c
EM=>DM em B C ¬[¬b×¬c] | inj₂ ¬b | inj₂ ¬c =
  let ¬b×¬c : ¬ B × ¬ C
      ¬b×¬c = ¬b , ¬c
  in  ⊥-elim (¬[¬b×¬c] ¬b×¬c)


DM=>EM : (∀ (A B : Set) -> de-morgan A B)
      -> (∀ (C : Set) -> excluded-middle C)
DM=>EM dm C = dm C (¬ C) (lemma C)
  where
  lemma : ∀ (C : Set) -> ¬ (¬ C × ¬ (¬ C))
  lemma C (¬c , ¬¬c) = ¬¬c ¬c

IAD=>EM : (∀ (A B : Set) -> implication-as-disjunction A B)
       -> (∀ (C : Set) -> excluded-middle C)
IAD=>EM iad C = swap (iad C C (λ c → c))


