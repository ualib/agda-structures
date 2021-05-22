---
layout: default
title : agda-imports module
date : 2021-05-20
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module agda-imports where

open import Agda.Builtin.Equality using (_≡_; refl) public
open import Agda.Builtin.Bool using (true; false) public
open import Agda.Primitive using (Level ; lsuc ; _⊔_)
 renaming (   Set to Type
          ;  Setω to Typeω
          ; lzero to ℓ₀
          ) public

open import Data.Empty using (⊥) public

open import Data.Product using ( _,_ ; Σ ; Σ-syntax ; _×_; ∃; ∃-syntax)
 renaming ( proj₁ to fst
 ; proj₂ to snd ) public

open import Data.Sum.Base using (_⊎_)
open import Function.Base using (_∘_; id) public
open import Level public using ( Lift; lift; lower) public
open import Relation.Binary.Core using (_⇒_;_=[_]⇒_) public
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; cong-app) public
open import Relation.Unary using (∅; Pred; _∪_; _∈_; _⊆_; ｛_｝) public
open import Relation.Nullary using (Dec; _because_; ofʸ) public

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀



\end{code}
