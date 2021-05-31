---
layout: default
title : lattices.base module
date : 2021-05-25
author: William DeMeo
---

\begin{code}

-- {-# OPTIONS --without-K --exact-split --safe #-}
{-# OPTIONS --exact-split --safe #-}

module lattices.base where

open import agda-imports
open import overture.preliminaries
open import relations.continuous
open import structures.base

private
 variable
  ℓ : Level
  C : Set ℓ

_∨_ : (m n : ℕ) → ℕ
zero ∨ n = n
suc m ∨ zero = suc m
suc m ∨ suc n = suc (m ∨ n)

\end{code}

**Example (Semilattice)**. A (meet-)semilattice `𝑨 = (A , ∧)` is a type `A` along with a binary operation `∧ : A → A → A`.

Here is how we could define the operational signature for semilattices as a member of the type `Signature`.  We will then define an empty relational signature and then define the type of semilattice as a structure with a single binary peration and no relations.

\begin{code}

data semilattice-op : Type ℓ₀ where
 ∧ : semilattice-op



-- The relational signature (semilattices have no relations)
semilattice-rels : signature
semilattice-rels = record { symbol = 𝟘 ; arity = λ () }


-- The operational signature (semilattices have one binary operation)
semilattice-ops : signature
semilattice-ops = record { symbol = semilattice-op ; arity = λ ∧ → 𝟚 }

-- The two element semilattice
𝟚-semilattice : structure {ℓ₀} semilattice-rels  {ℓ₀} semilattice-ops
𝟚-semilattice = record { carrier = 𝟚 ; rel = λ() ; op = λ ∧ x → min (x 𝟎) (x 𝟏) }
 where
 min : 𝟚 → 𝟚 → 𝟚
 min 𝟎 b = 𝟎
 min 𝟏 b = b


-- -- The operational signature (semilattices have one binary operation)
-- semilattice-ops : signature
-- semilattice-ops = record { symbol = semilattice-op ; ar = λ ∧ → Bool }

-- -- The two element semilattice
-- 𝟚-semilattice : structure {ℓ₀} semilattice-rels  {ℓ₀} semilattice-ops
-- 𝟚-semilattice = record { univ = Bool ; srel = λ() ; sop = λ ∧ x → min (x ff) (x tt) }
--  where
--  min : Bool → Bool → Bool
--  min ff b = ff
--  min tt b = b





\end{code}

Thus, the signature for a monoid consists of two operation symbols, `e` and `·`, and a function `λ { e → 𝟘; · → 𝟚 }` which maps `e` to the empty type 𝟘 (since `e` is the nullary identity) and maps `·` to the two element type 𝟚 (since `·` is binary).











∨-comm : {m n : ℕ} → m ∨ n ≡ n ∨ m
∨-comm {zero}{zero} = refl
∨-comm {zero}{suc n} = refl
∨-comm {suc m}{zero} = refl
∨-comm {suc m}{suc n} = γ
 where
 IH : m ∨ n ≡ n ∨ m
 IH = ∨-comm{m}{n}
 γ : suc (m ∨ n) ≡ suc (n ∨ m)
 γ = cong suc IH

right-id : ∀ {j} → j ∨ zero ≡ j
right-id {zero} = refl
right-id {suc j} = refl

left-id : ∀ {j} → zero ∨ j ≡ j
left-id {zero} = refl
left-id {suc j} = refl

≡→≤ : ∀ {i}{j} → i ≡ j → i ≤ j
≡→≤ {zero}{j} ij = z≤n
≡→≤ {suc i}{suc .i} refl = s≤s (≡→≤ refl)

suc-≤-cong : ∀ {m n} → suc m ≤ suc n → m ≤ n
suc-≤-cong (s≤s x) = x

≤-substʳ : (i j k : ℕ) → i ≤ k → k ≡ j → i ≤ j
≤-substʳ i j .j i≤k refl = i≤k

≤-substˡ : (i j k : ℕ) → i ≤ k → i ≡ j → j ≤ k
≤-substˡ i .i k i≤k refl = i≤k

-------------------------------------
-- _≤_ correspondence (∨ ⇒ ≤)
∨→≤ : ∀{i}{j} → i ∨ j ≡ j → i ≤ j
∨→≤ {zero} x = z≤n
∨→≤ {suc i} {suc j} x = s≤s (∨→≤ (suc-injective x))


----------------------------------
-- _≤_ correspondence (≤ ⇒ ∨)
≤→∨ : ∀{i}{j} → i ≤ j → i ∨ j ≡ j
≤→∨ {i}{zero} ub = trans (cong (λ x → x ∨ zero) (n≤0⇒n≡0 ub)) left-id

≤→∨ {zero}{suc j} ub = refl
≤→∨ {suc i}{suc j} ub = cong suc (≤→∨ (suc-≤-cong ub))






-- We use the dec type to prove that ℕ has decidable equality type.
data dec (B : Set) : Set where
  yes : B → dec B
  no : ¬ B → dec B

sn≡sm→n≡m : ∀ n m → suc n ≡ suc m → n ≡ m
sn≡sm→n≡m n .n refl = refl

-- ℕ-dec is an alias for ℕ-decidable-equality, which proves that ℕ has decidable equality.
-- That is, for all i j : ℕ, we can decide whether i ≡ j is true or false.
ℕ-dec
 ℕ-decidable-equality : (i j : ℕ) → dec (i ≡ j)
ℕ-decidable-equality zero zero = yes refl
ℕ-decidable-equality zero (suc j) = no (λ ())
ℕ-decidable-equality (suc i) zero = no (λ ())
ℕ-decidable-equality (suc i) (suc j) = γ
 where
 IH : dec (i ≡ j)          -- a : A
 IH = ℕ-decidable-equality i j
 IH→γ : dec (i ≡ j) → dec (suc i ≡ suc j)   -- f : A → B
 IH→γ (yes x) = yes (cong suc x)
 IH→γ (no x) = no (λ si≡sj → ⊥-elim (x (sn≡sm→n≡m i j si≡sj)))
 γ : dec (suc i ≡ suc j)
 γ = IH→γ IH

ℕ-dec = ℕ-decidable-equality

-- We use `Compare n m`, when we don't know anything about n m.
data Compare (n m : ℕ) : Set where
 less    : n < m → Compare n m
 equal   : n ≡ m → Compare n m
 greater : n > m → Compare n m

-- Here is how we construct an element of type `Compare n m`
-- (besides the fact that they are natural numbers).
compare : ∀ (m n : ℕ) → Compare m n
compare zero zero = equal refl
compare zero (suc n) = less (s≤s z≤n)
compare (suc m) zero = greater (s≤s z≤n)
compare (suc m) (suc n) = succompare (compare m n)
 where
 succompare : Compare m n → Compare (suc m) (suc n)
 succompare (less n<m) = less (s≤s n<m)
 succompare (equal n≡m) = equal (cong suc n≡m)
 succompare (greater n>m) = greater (s≤s n>m)


data Comparenew  : ℕ → ℕ → Set where
 below     : ∀ {n m : ℕ} → n < m → Comparenew n m
 above   : ∀ {n m : ℕ} → n ≥ m → Comparenew n m

comparenew : (n m : ℕ) → Comparenew n m
comparenew n zero          = above z≤n
comparenew zero (suc m)    = below (s≤s z≤n)
comparenew (suc n) (suc m) = succompare (comparenew n m)
 where
  succompare : {n m : ℕ} → Comparenew n m → Comparenew (suc n) (suc m)
  succompare (below n<m) = below (s≤s n<m)
  succompare (above n≥m) = above (s≤s n≥m)


-- Uniqueness of ≡ and < proofs for ℕ ------------------------------------------------
UIP : ∀ {m n : ℕ} (p q : m ≡ n) → p ≡ q
UIP refl refl = refl

comp-≡ : ∀ {i j} → (p : i ≡ j)(c : Compare i j) → c ≡ equal p
comp-≡ p (less q) = ⊥-elim (<-irrefl p q)
comp-≡ p (equal q) = cong equal (UIP q p)
comp-≡ p (greater q) = ⊥-elim (<-irrefl (p ⁻¹) q)

compii : ∀ {i} → compare i i ≡ equal refl
compii {i} = comp-≡ refl (compare i i)


<-UIP : ∀ {m n : ℕ} (p q : m < n) → p ≡ q
<-UIP = <-irrelevant

≤-UIP : ∀ {m n : ℕ} (p q : m ≤ n) → p ≡ q
≤-UIP = ≤-irrelevant

≥-UIP : ∀ {m n : ℕ} (p q : m ≥ n) → p ≡ q
≥-UIP = ≤-irrelevant

comp-< : ∀ {i j} → (p : i < j)(c : Compare i j) → c ≡ less p
comp-< p (less x) = cong less (<-UIP x p)
comp-< p (equal x) = ⊥-elim (<-irrefl x p)
comp-< p (greater x) = ⊥-elim (<⇒≯ p x)

compnew-< : ∀ {i j} → (p : i < j)(c : Comparenew i j) → c ≡ below p
compnew-< p (below x) = cong below (<-UIP x p)
compnew-< p (above x) = ⊥-elim (<⇒≱ p x)

compnew-≥ : ∀ {i j} → (p : i ≥ j)(c : Comparenew i j) → c ≡ above p
compnew-≥ p (below x) = ⊥-elim (<⇒≱  x p)
compnew-≥ p (above x) = cong above (≥-UIP x p)




<-cong : (i j k : ℕ) → i < k → k ≡ j → i < j
<-cong i j .j i<k refl = i<k

si≮si : (i : ℕ) → ¬ (suc i < suc i)
si≮si i x = <-irrefl refl x

<→≤ : (i j : ℕ) → i < j → suc i ≤ j
<→≤ i (suc j) i<j = i<j

≤<→< : (i j k : ℕ) → i ≤ j → j < k → i < k
≤<→< i j k i≤j j<k = <-transʳ i≤j j<k

j<i<sj-elim : (i j : ℕ) → j < i → i < suc j → ⊥
j<i<sj-elim (suc i) j j<i i<sj = ⊥-elim (si≮si j sj<sj)
 where
 sj≤si : suc j ≤ suc i
 sj≤si = <→≤ j (suc i) j<i

 sj<sj : suc j < suc j
 sj<sj = ≤<→< (suc j) (suc i) (suc j) sj≤si i<sj


n≥n : ∀ n → n ≥ n
n≥n zero = z≤n
n≥n (suc n) = s≤s (n≥n n)


m≤m∨n : ∀ m n → m ≤ m ∨ n
m≤m∨n zero n = z≤n
m≤m∨n (suc m) zero = ≤-reflexive refl
m≤m∨n (suc m) (suc n) = s≤s (m≤m∨n m n)

\end{code}


















-- open import Data.Product using (_,_; Σ; Σ-syntax; _×_)

-- open import Agda.Builtin.Nat renaming (Nat to ℕ) using (_-_)
-- open import Agda.Builtin.Sigma using (fst; snd)
-- -- open import Agda.Builtin.Bool using (true; false)

-- -- open import Data.Bool.Base using (true; false)



-- open import Level renaming (suc to lsuc; zero to lzero)

-- -- open import Relation.Binary.Definitions using (Transitive)
-- -- import Relation.Binary.PropositionalEquality as Eq
-- -- open Eq using (_≡_; refl; cong; sym; trans; cong-app; subst; module ≡-Reasoning)
-- -- open ≡-Reasoning

-- -- open import Relation.Nullary using (Dec; _because_; ofʸ)



-- ; _≮__+_; _<_; _>_; _≤_; _≥_; pred;
