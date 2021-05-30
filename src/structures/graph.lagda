---
layout: default
title : structures.graph module
date : 2021-05-26
author: William DeMeo
---

This module implements the graph of a structure.  (See Definition 2 of https://arxiv.org/pdf/2010.04958v2.pdf )

Definition [Graph of a structure]. Let 𝑨 be an (𝑅,𝐹)-structure (relations from 𝑅 and operations from 𝐹).
The *graph* of 𝑨 is the structure Gr 𝑨 with the same domain as 𝑨 with relations from 𝑅 and together with a (k+1)-ary relation symbol G 𝑓 for each 𝑓 ∈ 𝐹 of arity k, which is interpreted in Gr 𝑨 as all tuples (t , y) ∈ Aᵏ⁺¹ such that 𝑓 t ≡ y.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import agda-imports
open import overture.preliminaries
open import relations.continuous
open import structures.base
open import homs.base

module structures.graph {𝑅 𝐹 : signature}  where

private variable α ρ₀ : Level

Gr-sig : signature → signature → signature
Gr-sig 𝑅 𝐹 = record { symbol = symbol 𝑅 ⊎ symbol 𝐹 ; arity = arty }
 where
 arty : symbol 𝑅 ⊎ symbol 𝐹 → Arity
 arty (inl 𝑟) = (arity 𝑅) 𝑟
 arty (inr 𝑓) = (arity 𝐹) 𝑓 ⊎ 𝟙


Gr : structure {α} 𝑅 𝐹 → structure (Gr-sig 𝑅 𝐹) Sig∅
Gr 𝑨 = record { carrier = carrier 𝑨 ; rel = split ; op = λ () }
 where
  split : (𝑟 : symbol 𝑅 ⊎ symbol 𝐹) → Rel (carrier 𝑨)
  split (inl 𝑟) arg = rel 𝑨 𝑟 arg -- (rel 𝑨) 𝑟 arg
  split (inr 𝑓) args = op 𝑨 𝑓 (args ∘ inl) ≡ args (inr 𝟎)



hom→Grhom : {𝑨 𝑩 : structure {ℓ₀} 𝑅 {ℓ₀} 𝐹} → hom 𝑨 𝑩 → hom (Gr 𝑨) (Gr 𝑩)
hom→Grhom {𝑨}{𝑩} (h , hhom) = h , (i , ii)
 where
  i : is-hom-rel (Gr 𝑨) (Gr 𝑩) h
  i (inl 𝑟) a x = ∣ hhom ∣ 𝑟 a x
  i (inr 𝑓) a x = γ
   where
   homop : h (op 𝑨 𝑓 (a ∘ inl)) ≡ op 𝑩 𝑓 (h ∘ (a ∘ inl))
   homop = (snd hhom) 𝑓 (a ∘ inl)

   γ : op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡ h (a (inr 𝟎))
   γ = op 𝑩 𝑓 (h ∘ (a ∘ inl)) ≡⟨ ≡-sym homop ⟩
       h (op 𝑨 𝑓 (a ∘ inl))   ≡⟨ cong h x ⟩
       h (a (inr 𝟎))           ∎
  ii : is-hom-op (Gr 𝑨) (Gr 𝑩) h
  ii = λ ()


Grhom→hom : {𝑨 𝑩 : structure {ℓ₀} 𝑅 {ℓ₀} 𝐹} → hom (Gr 𝑨) (Gr 𝑩) → hom 𝑨 𝑩
Grhom→hom {𝑨}{𝑩} (h , hhom) = h , (i , ii)
 where
  i : is-hom-rel 𝑨 𝑩 h
  i R a x = fst hhom (inl R) a x
  ii : is-hom-op 𝑨 𝑩 h
  ii f a = γ
   where
   split : arity 𝐹 f ⊎ 𝟙 → carrier 𝑨
   split (inl x) = a x
   split (inr y) = op 𝑨 f a
   γ : h (op 𝑨 f a) ≡ op 𝑩 f (λ x → h (a x))
   γ = ≡-sym (fst hhom (inr f) split refl )



 -- comm-rel : (symbol 𝑅) → ((univ 𝑨) → (univ 𝑩)) → Type α
 -- comm-rel 𝑟 h = ∀ a → ((srel 𝑨) 𝑟 a) → ((srel 𝑩) 𝑟) (h ∘ a)

 -- is-hom-rel : ((univ 𝑨) → (univ 𝑩)) → Type α
 -- is-hom-rel h = ∀ R →  comm-rel R h

 -- comm-op : (symbol 𝐹) → ((univ 𝑨) → (univ 𝑩)) → Type (α ⊔ β)
 -- comm-op f h = ∀ a → h (((sop 𝑨) f) a) ≡ ((sop 𝑩) f) (h ∘ a)


 -- is-hom-op : ((univ 𝑨) → (univ 𝑩)) → Type (α ⊔ β)
 -- is-hom-op h = ∀ f → comm-op f h

 -- is-hom : ((univ 𝑨) → (univ 𝑩)) → Type (α ⊔ β)
 -- is-hom h = is-hom-rel h × is-hom-op h

 -- hom : Type (α ⊔ β)
 -- hom = Σ[ h ∈ ((univ 𝑨) → (univ 𝑩)) ] is-hom h
 
