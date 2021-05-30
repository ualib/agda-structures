---
layout: default
title : Structures.Base module
date : 2021-05-20
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures.Base where

open import agda-imports
open import overture.preliminaries
open import relations.continuous

-- Inhabitants of Signature type are pairs, (s , ar), where s is an operation or
-- relation symbol and ar its arity.
Signature : Type ℓ₁
Signature = Σ[ F ∈ Type ℓ₀ ] (F → Arity)


module _ {α : Level} (𝑅 : Signature) {ρ : Level} (𝐹 : Signature) where

 Structure : Type (lsuc (α ⊔ ρ))
 Structure  =
  Σ[ A ∈ Type α ]                        -- the domain of the structure is A
   ( ((r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r}{ρ})  -- the interpretations of the relation symbols
   × ((f : ∣ 𝐹 ∣) → Op A{snd 𝐹 f}) )     -- the interpretations of the operation symbols


RStructure : {α : Level} → Signature → {ρ : Level} → Type (lsuc (α ⊔ ρ))
RStructure {α} 𝑅 {ρ} = Σ[ A ∈ Type α ] ∀(r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r} {ρ}

AStructure : {α : Level} → Signature → Type (lsuc α)
AStructure {α} 𝐹 = Σ[ A ∈ Type α ] ∀ (f : ∣ 𝐹 ∣) → Op A {snd 𝐹 f}

-- Reducts
module _ {α ρ : Level}{𝑅 𝐹 : Signature} where
 Structure→RStructure : Structure {α} 𝑅 {ρ} 𝐹 → RStructure 𝑅
 Structure→RStructure (A , (ℛ , _)) = A , ℛ

 Structure→AStructure : Structure {α} 𝑅 {ρ} 𝐹 → AStructure 𝐹
 Structure→AStructure (A , (_ , ℱ)) = A , ℱ

  -- Syntax for interpretation of relations and operations.
 _⟦_⟧ᵣ : (𝒜 : Structure {α} 𝑅 {ρ} 𝐹)(𝑟 : fst 𝑅) → Rel (fst 𝒜) {snd 𝑅 𝑟} {ρ}
 𝒜 ⟦ 𝑟 ⟧ᵣ = λ a → (∣ snd 𝒜 ∣ 𝑟) a

 _⟦_⟧ₒ : (𝒜 : Structure {α} 𝑅 {ρ} 𝐹)(𝑓 : fst 𝐹) → Op (fst 𝒜) {snd 𝐹 𝑓}
 𝒜 ⟦ 𝑓 ⟧ₒ = λ a → (snd (snd 𝒜) 𝑓) a

 _ʳ_ : (𝑟 : fst 𝑅)(𝒜 : Structure {α} 𝑅 {ρ} 𝐹) → Rel (fst 𝒜){(snd 𝑅) 𝑟}{ρ}
 𝑟 ʳ 𝒜 = λ a → (𝒜 ⟦ 𝑟 ⟧ᵣ) a

 _ᵒ_ : (𝑓 : fst 𝐹)(𝒜 : Structure {α} 𝑅 {ρ} 𝐹) → Op (fst 𝒜){snd 𝐹 𝑓}
 𝑓 ᵒ 𝒜 = λ a → (𝒜 ⟦ 𝑓 ⟧ₒ) a

 Compatible : {ρ' : Level}(𝑨 : Structure {α} 𝑅 {ρ} 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
 Compatible 𝑨 r = ∀ 𝑓 → (𝑓 ᵒ 𝑨) |: r

 Compatible' : {ρ' : Level}(𝑨 : Structure {α} 𝑅 {ρ} 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
 Compatible' 𝑨 r = ∀ 𝑓 → compatible-op (𝑓 ᵒ 𝑨) r

 open Lift

 Lift-op : {I : Arity}{A : Type α} → Op A{I} → (ℓ : Level) → Op (Lift ℓ A){I}
 Lift-op f ℓ = λ x → lift (f (λ i → lower (x i)))

 Lift-rel : {I : Arity}{A : Type α} → Rel A {I}{ρ} → (ℓ : Level) → Rel (Lift ℓ A) {I}{ρ}
 Lift-rel r ℓ x = r (λ i → lower (x i))

 Lift-struc : Structure {α} 𝑅 {ρ} 𝐹 → (ℓ : Level) → Structure {α ⊔ ℓ} 𝑅 {ρ} 𝐹
 Lift-struc 𝑨 ℓ = Lift ℓ ∣ 𝑨 ∣ , (lrel , lop )
  where
  lrel : (r : ∣ 𝑅 ∣) → Rel (Lift ℓ ∣ 𝑨 ∣){snd 𝑅 r}{ρ}
  lrel r = λ x → ((r ʳ 𝑨) (λ i → lower (x i)))
  lop : (f : ∣ 𝐹 ∣) → Op (Lift ℓ ∣ 𝑨 ∣) {snd 𝐹 f}
  lop f = λ x → lift ((f ᵒ 𝑨)( λ i → lower (x i)))

\end{code}






-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------



























-- Alternative development using records

record signature : Type ℓ₁ where
field
symbol : Type ℓ₀
ar : symbol → Arity

open signature public


record structure {α : Level} (𝑅 : signature) {ρ : Level} (𝐹 : signature) : Type (lsuc (α ⊔ ρ)) where
field
univ : Type α
rel  : ∀ (𝑟 : symbol 𝑅) → Rel univ{ar 𝑅 𝑟}{ρ}  -- interpretations of relations
op   : ∀ (𝑓 : symbol 𝐹) → Op univ{ar 𝐹 𝑓}  -- interpretations of operations

open structure public

compatible : {α ρ : Level}{𝑅 𝐹 : signature}(𝑨 : structure {α} 𝑅 {ρ} 𝐹) → BinRel (univ 𝑨) ρ  → Type (α ⊔ ρ)
compatible {𝑅 = 𝑅}{𝐹} 𝑨 r = ∀ (𝑓 : symbol 𝐹)(u v : (ar 𝐹) 𝑓 → univ 𝑨) → ((op 𝑨) 𝑓) |: r


-- Some examples (of finite signatures)
-- The signature with...
-- ... no symbols  (e.g., sets)
Sig∅ : signature
Sig∅ = record { symbol = 𝟘 ; ar = λ () }

-- ... one nulary symbol (e.g., pointed sets)
Sig-0 : signature
Sig-0 = record { symbol = 𝟙 ; ar = λ 𝟎 → 𝟘 }

Sig-1 : signature -- ...one unary
Sig-1 = record { symbol = 𝟙 ; ar = λ 𝟎 → 𝟙 }

-- ...one binary symbol (e.g., magmas, semigroups, semilattices)
Sig-2 : signature
Sig-2 = record { symbol = 𝟙 ; ar = λ 𝟎 → 𝟚 }

-- ...one nulary and one binary (e.g., monoids)
Sig-0-1 : signature
Sig-0-1 = record { symbol = 𝟚 ; ar = λ{ 𝟎 → 𝟘 ; 𝟏 → 𝟚 } }

-- ...one nulary, one unary, and one binary (e.g., groups)
Sig-0-1-2 : signature
Sig-0-1-2 = record { symbol = 𝟛 ; ar = λ{ 𝟎 → 𝟘 ; 𝟏 → 𝟙 ; 𝟐 → 𝟚 } }




