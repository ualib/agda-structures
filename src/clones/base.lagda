---
layout: default
title : clones.base
date : 2021-05-31
author: William DeMeo
---


## Clones (See §4.1 of Bergman)

Let A be a set. For every natural number n let Opₙ(A) denote the set of all n-ary operations on A. Put another way, Opₙ(A) = A^(Aⁿ). Let Op(A) = ⋃ₙ Opₙ(A) be the set of all operations on A. For each k < n there is an n-ary operation pⁿₖ(x₁, ..., xₙ) = xₖ, called the k-ih projection operation.  Let n and k be natural numbers, and suppose that f ∈ Opₙ(A) and g₁, ..., gₙ ∈ Opₖ(A). Then we define a new k-ary operation f[g₁,..., gₙ] by:

(x₁, x₂, ..., xₙ) ↦ f (g₁(x₁, ..., xₖ), ..., gₙ(x₁, ..., xₖ))

called the generalized composite of f with g₁, ..., gₙ. Note that, unlike the ordinary composition of unary operation, the generalized composite only exists when all of the ranks match up correctly.

There is one peculiarity that should be pointed out. Suppose that f is a nullary operation with value c ∈ A. Then f[ ], the result of composing f with 0-many n-ary operations is the n-ary operation (x₁,..., xₙ) ↦ c. Thus, starting from a nullary operation with constant value c, we can construct an n-ary operation with constant value c for all n.

Just as the set of unary operations forms a monoid under the operation of composition, we can form a kind of algebraic structure whose elements are members of Op(A) with the operation of generalized composition.

Definition 4.1. Let A be a nonempty set. A **clone** on A is a subset C of Op(A) that contains all projection operations and is closed under generalized composition.

Example 4.2. For each nonempty set A, both Op(A) and Proj(A) := {pⁿₖ : 0 < k ≤ n } are clones



\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import agda-imports
open import overture.preliminaries
open import relations.extensionality
open import relations.continuous
open import structures.base
-- open import homs.base

module clones.base where


private
  variable
    α β γ ρ ρ₀ ρ₁ : Level
    A : Set α
    B : Set β
    C : Set γ

Op[_] : (A : Type α) (n : ℕ) → Type α
Op[ A ] n = (Fin n → A) → A

-- All operations on A
O[_] : (A : Type α) → Type α
O[ A ] = Σ[ n ∈ ℕ ] Op[ A ] n


-- The general composition of an n-ary operation f with n k-ary operations, G : Fin n → Op[ A ] k.
_∘[_]_ : {A : Type α}{n : ℕ} → Op[ A ] n → (k : ℕ)(G : (i : Fin n) → Op[ A ] k) → Op[ A ] k
f ∘[ k ] G = λ j → f (λ i → G i j)

-- Projections.
-- We denote the n-ary projections by π[ n ] and the i-th one of these by π[ n ] i.
π[_] : {A : Type α}(n : ℕ) → (i : Fin n) → Op[ A ] n
π[ n ] i x = x i

-- The collection of all projections.
Proj : {A : Type α} → Pred ( O[ A ] ) α
Proj{A = A} (n , p) = Σ[ i ∈ Fin n ] (∀ (x : Fin n → A) → p x ≡ x i)

-- General compositions of projections are projections.
ProjComp : {n k : ℕ} {f : Op[ A ] n}(G : (i : Fin n) → Op[ A ] k)
  →        (n , f) ∈ Proj → (∀ i → (k , G i) ∈ Proj)
           ----------------------------------------------------
  →        (k , f ∘[ k ] G) ∈ Proj

ProjComp G (j , p) q = (fst (q j)) , λ x → ≡-trans (p (λ z → G z x)) (snd (q j) x)


data Clone {α : Level}{A : Type α}(𝒦 : Pred( O[ A ] ) α) : Pred( O[ A ] ) α
 where
 cbase : (n : ℕ)(i : Fin n) → (n , π[ n ] i) ∈ Clone 𝒦
 comp : (n k : ℕ) (f : Op[ A ] n)(G : (i : Fin n) → Op[ A ] k)
  →     (n , f) ∈ Clone 𝒦 → (∀ i → (k , G i) ∈ Clone 𝒦) → (k , f ∘[ k ] G) ∈ Clone 𝒦


IsClone : {α ρ : Level}{A : Type α}(𝒦 : Pred( O[ A ] ) α) → Type α
IsClone 𝒦 = Clone 𝒦 ⊆ 𝒦

ProjIsClone : {A : Type α} → (IsClone{α}{ρ}{A}) Proj
ProjIsClone {A = A} (cbase n i) = i , (λ x → refl)
ProjIsClone{α}{ρ} {A = A} (comp n k f G x x₁) = Goal
 where
 PG : (i : Fin n) → (k , G i) ∈ Proj
 PG i = ProjIsClone{α}{ρ} (x₁ i)
 Pf : (n , f) ∈ Proj
 Pf = ProjIsClone {α}{ρ} x

 Goal : (k , (f ∘[ k ] G)) ∈ Proj
 Goal = ProjComp{n = n}{f = f} G Pf PG


-- Term Equivalence of General Structures
-- -- alias (so that we can easily change the level of X later if necessary)
-- χ : Level
-- χ = ℓ₀

-- _⟦_⟧ : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){X : Type χ } → Term X → Op (carrier 𝑨) {X}
-- 𝑨 ⟦ ℊ x ⟧ = λ η → η x
-- 𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → (op 𝑨 𝑓) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)

-- Clo : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){X : Type χ } → Pred (Op (carrier 𝑨) {X}) α
-- Clo 𝑨 {X} = λ (o : Op (carrier 𝑨) {X}) → Σ[ t ∈ Term X ] (o ≡ 𝑨 ⟦ t ⟧)

-- TE : {U : Type α} {X : Type χ} → BinRel (Pred (Op U {X}) α) α
-- TE CA CB = CA ⊆ CB × CB ⊆ CA
