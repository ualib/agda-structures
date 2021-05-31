---
layout: default
title : agda-imports module
date : 2021-05-20
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module agda-imports where

open import Agda.Builtin.Bool using (Bool; true; false) public
open import Agda.Primitive using (Level; lsuc; _⊔_)
 renaming (Set to Type;Setω to Typeω; lzero to ℓ₀) public
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext) public


-- Imports from Data module of Agda Standard Library
open import Data.Empty public
open import Data.Fin.Base renaming (lift to finLift) public
open import Data.Nat using (ℕ; zero; suc) public -- ; _<_; _>_; _≤_; _≥_; s≤s; z≤n; pred) public
open import Data.Nat.Properties
 using (<-irrefl; <-irrelevant; ≤-irrelevant; <⇒≯; <⇒≱; suc-injective; n≤0⇒n≡0; <-transʳ; ≤-reflexive) public
open import Data.Product using ( _,_ ; Σ ; Σ-syntax ; _×_; ∃; ∃-syntax)
 renaming ( proj₁ to fst ; proj₂ to snd ) public
open import Data.Sum.Base using (_⊎_) -- (we might also want [_,_] )
 renaming ( inj₁ to inl ; inj₂ to inr ) public
open import Data.Unit.Polymorphic.Base public


open import Function.Base using (_∘_; id) public
open import Level public using ( Lift; lift; lower) public


-- Imports from Relation module of Agda Standard Library
open import Relation.Binary.Core using (_⇒_;_=[_]⇒_) public
open import Relation.Binary.PropositionalEquality as Eq
open Eq renaming (sym to ≡-sym; trans to ≡-trans)
 using (_≡_; refl; cong; cong-app; module ≡-Reasoning) public
open ≡-Reasoning public
open import Relation.Nullary using (¬_; Dec; _because_; ofʸ) public
open import Relation.Unary using (∅; Pred; _∪_; _∈_; _⊆_; ｛_｝; ⋂) public

ℓ₁ : Level
ℓ₁ = lsuc ℓ₀



\end{code}
