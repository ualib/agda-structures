---
layout: default
title : structures.base module
date : 2021-05-20
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module structures.base where

open import agda-imports
open import overture.preliminaries
open import relations.continuous

-- Inhabitants of Signature type are pairs, (s , ar), where s is an operation or
-- relation symbol and ar its arity.
Signature : Type ℓ₁
Signature = Σ[ F ∈ Type ℓ₀ ] (F → Arity)

Structure : (𝑅 𝐹 : Signature){β : Level} → Type (lsuc β)
Structure 𝑅 𝐹 {β} =
 Σ[ B ∈ Type β ]                    -- the domain of the structure is B
  ( ((r : ∣ 𝑅 ∣) → rel(∥ 𝑅 ∥ r) B)  -- the interpretations of the relation symbols
  × ((f : ∣ 𝐹 ∣) → Op(∥ 𝐹 ∥ f) B) ) -- the interpretations of the operation symbols

RStructure : (β : Level) → Signature → Type (lsuc β)
RStructure β 𝑅 = Σ[ B ∈ Type β ] ∀(r : ∣ 𝑅 ∣) → rel(∥ 𝑅 ∥ r) B

AStructure : (β : Level) → Signature → Type (lsuc β)
AStructure β 𝐹 = Σ[ B ∈ Type β ] ∀ (f : ∣ 𝐹 ∣) → Op (∥ 𝐹 ∥ f) B

-- Reducts
Structure→AStructure : {𝑅 𝐹 : Signature}{β : Level} → Structure 𝑅 𝐹 → AStructure β 𝐹
Structure→AStructure (B , (ℛ , ℱ)) = B , ℱ

Structure→RStructure : {𝑅 𝐹 : Signature}{β : Level} → Structure 𝑅 𝐹 → RStructure β 𝑅
Structure→RStructure (B , (ℛ , ℱ)) = B , ℛ


module _ {𝑅 𝐹 : Signature}  where
{- Let 𝑅 and 𝐹 be signatures and let ℬ = (B , (ℛ , ℱ)) be an (𝑅, 𝐹)-structure.
   - If `r : ∣ 𝑅 ∣` is a relation symbol, then `rel ℬ r` is the interpretation of `r` in `ℬ`.
   - if `f : ∣ 𝐹 ∣` is an opereation symbol, then `op ℬ f` is the interpretation
   of `f` in `ℬ`. -}

  -- Syntax for interpretation of relations and operations.
  _⟦_⟧ᵣ : (ℬ : Structure 𝑅 𝐹 {β})(R : fst 𝑅) → rel ((snd 𝑅) R) (fst ℬ)
  ℬ ⟦ R ⟧ᵣ = λ b → (∣ snd ℬ ∣ R) b

  _⟦_⟧ₒ : (ℬ : Structure 𝑅 𝐹 {β})(𝑓 : fst 𝐹) → Op ((snd 𝐹) 𝑓) (fst ℬ)
  ℬ ⟦ 𝑓 ⟧ₒ = λ b → (snd (snd ℬ) 𝑓) b

  _ʳ_ : (R : fst 𝑅)(ℬ : Structure 𝑅 _ {β}) → rel ((snd 𝑅) R) (fst ℬ)
  R ʳ ℬ = λ b → (ℬ ⟦ R ⟧ᵣ) b

  _ᵒ_ : (𝑓 : fst 𝐹)(ℬ : Structure _ 𝐹 {β}) → Op ((snd 𝐹) 𝑓) (fst ℬ)
  𝑓 ᵒ ℬ = λ b → (ℬ ⟦ 𝑓 ⟧ₒ) b

  compatible : (𝑩 : Structure 𝑅 𝐹 {β}) → BinRel (fst 𝑩) α  → Type (β ⊔ α)
  compatible 𝑩 r = ∀ 𝑓 → (𝑓 ᵒ 𝑩) |: r



-- Alternative development using records

record signature : Type ℓ₁ where
 field
  symbol : Type ℓ₀
  ar : symbol → Arity

open signature


record structure (𝑅 𝐹 : signature) {β : Level} : Type (lsuc β) where
 field
  univ : Type β
  srel  : ∀ (r : symbol 𝑅) → rel(ar 𝑅 r) univ  -- interpretations of relations
  sop   : ∀ (f : symbol 𝐹) → Op (ar 𝐹 f) univ  -- interpretations of operations

open structure

compatible' : {𝑅 𝐹 : signature}{β : Level}(𝑩 : structure 𝑅 𝐹 {β}){α : Level} → BinRel (univ 𝑩) α  → Type (α ⊔ β)
compatible' {𝑅}{𝐹} 𝑩 r = ∀ (𝑓 : symbol 𝐹)(u v : (ar 𝐹) 𝑓 → univ 𝑩) → ((sop 𝑩) 𝑓) |: r




\end{code}


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------



































