---
layout: default
title : lattices.properties module
date : 2021-05-25
author: William DeMeo
---

\begin{code}

-- {-# OPTIONS --without-K --exact-split --safe #-}
{-# OPTIONS --exact-split --safe #-}

open import Data.Nat using (ℕ; zero; suc; _<_; _>_; _≤_; _≥_; s≤s; z≤n)
-- ; _≮__+_; _<_; _>_; _≤_; _≥_; pred;

open import Data.Nat.Properties using (≤⇒≯; <⇒≯; n≮n; n≤0⇒n≡0; n≤1+n; <⇒≱; <-irrefl; ≤-trans; <-trans; <-transʳ; suc-injective; <-irrelevant; ≤-irrelevant; ≤-reflexive)



module lattices.properties where

open import agda-imports
open import overture.preliminaries
open import relations.continuous
open import lattices.base


private
 variable
  ℓ : Level
  C : Set ℓ

-- We use the dec type to prove that ℕ has decidable equality type.
data dec (B : Set) : Set where
  yes : B → dec B
  no : ¬ B → dec B

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

\end{code}
