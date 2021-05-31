---
layout: default
title : terms.operations module
date : 2021-05-30
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import agda-imports
open import overture.preliminaries
open import overture.inverses
open import relations.extensionality
open import relations.continuous
open import structures.base
open import homs.base

module terms.operations {𝑅 𝐹 : signature} where

open import structures.congruences{𝑅 = 𝑅}{𝐹}
open import structures.products{𝑅 = 𝑅}{𝐹}
open import terms.base{𝑅 = 𝑅}{𝐹}

private variable α β ρ₀ ρ₁ : Level

-- alias (so that we can easily change the level of X later if necessary)
χ : Level
χ = ℓ₀

_⟦_⟧ : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){X : Type χ } → Term X → Op (carrier 𝑨) {X}
𝑨 ⟦ ℊ x ⟧ = λ η → η x
𝑨 ⟦ node 𝑓 𝑡 ⟧ = λ η → (op 𝑨 𝑓) (λ i → (𝑨 ⟦ 𝑡 i ⟧) η)

Clo : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){X : Type χ } → Pred (Op (carrier 𝑨) {X}) α
Clo 𝑨 {X} = λ (o : Op (carrier 𝑨) {X}) → Σ[ t ∈ Term X ] (o ≡ 𝑨 ⟦ t ⟧)

TE : {U : Type α} {X : Type χ} → BinRel (Pred (Op U {X}) α) α
TE CA CB = CA ⊆ CB × CB ⊆ CA

-- _≃ₜ_ : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹)(𝑩 : structure {α} 𝑅 {ρ₀} 𝐹) → Type ?
-- 𝑨 ≃ₜ 𝑩 = Σ[ p ∈ carrier 𝑨 ≡ carrier 𝑩 ] TE (Clo 𝑨) (Clo 𝑩)

free-lift-interp : funext ℓ₀ α → (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){X : Type χ }(η : X → carrier 𝑨)(p : Term X)
 →                 (𝑨 ⟦ p ⟧) η ≡ (free-lift 𝑨 η) p

free-lift-interp _ 𝑨 η (ℊ x) = refl
free-lift-interp fe 𝑨 η (node 𝑓 𝑡) = cong (op 𝑨 𝑓) (fe λ i → free-lift-interp fe 𝑨 η (𝑡 i))

term-interp : {X : Type χ} (𝑓 : symbol 𝐹){𝑠 𝑡 : arity 𝐹 𝑓 → Term X} → 𝑠 ≡ 𝑡 → node 𝑓 𝑠 ≡ (op (𝑻 X) 𝑓) 𝑡
term-interp 𝑓 {𝑠}{𝑡} st = cong (node 𝑓) st

term-gen : funext ℓ₀ χ → {X : Type χ}(p : carrier (𝑻 X)) → Σ[ q ∈ carrier (𝑻 X) ] (p ≡ (𝑻 X ⟦ q ⟧) ℊ)
term-gen _ (ℊ x) = (ℊ x) , refl
term-gen fe (node f t) = node f (λ i → ∣ term-gen fe (t i) ∣) , term-interp f (fe λ i → ∥ term-gen fe (t i) ∥ )

term-gen-agreement : (fe : funext ℓ₀ χ) {X : Type χ}(p : Term X) → (𝑻 X ⟦ p ⟧) ℊ ≡ (𝑻 X ⟦ ∣ term-gen fe p ∣ ⟧) ℊ
term-gen-agreement _ (ℊ x) = refl
term-gen-agreement fe {X} (node f 𝑡) = cong (op (𝑻 X) f) (fe λ x → term-gen-agreement fe (𝑡 x))

term-agreement : funext ℓ₀ χ → {X : Type χ}(p : Term X) → p ≡  (𝑻 X ⟦ p ⟧) ℊ
term-agreement fvx {X} p = ∥ term-gen fvx p ∥ ∙ (term-gen-agreement fvx p)⁻¹

-- Interpretation of terms in product algebras
module _ {X : Type χ }{I : Arity} where

 interp-prod : funext ℓ₀ α → (p : Term X)(𝒜 : I → structure {α} 𝑅 {ρ₀} 𝐹)(𝑎 : X → ∀ i → carrier (𝒜 i))
  →            (⨅ I 𝒜 ⟦ p ⟧) 𝑎 ≡ λ i →  (𝒜 i ⟦ p ⟧) (λ j → 𝑎 j i)

 interp-prod _ (ℊ x₁) 𝒜 𝑎 = refl
 interp-prod fe (node 𝑓 𝑡) 𝒜 𝑎 = cong (op (⨅ I 𝒜) 𝑓) (fe (λ x → interp-prod fe (𝑡 x) 𝒜 𝑎))

 interp-prod2 : funext ℓ₀ α → funext (χ ⊔ α) α → swelldef α → (p : Term X)(𝒜 : I → structure {α} 𝑅 {ρ₀} 𝐹)
  →             ⨅ I 𝒜 ⟦ p ⟧ ≡ (λ 𝑡 → (λ i → (𝒜 i ⟦ p ⟧) λ x → 𝑡 x i))

 interp-prod2 _ _ _  (ℊ x₁) 𝒜 = refl

 interp-prod2 fe₀ fe wd (node f t) 𝒜 = fe λ (tup : X → carrier ( ⨅ I 𝒜 )) →
  (op (⨅ I 𝒜) f)(λ s → ((⨅ I 𝒜) ⟦ t s ⟧) tup)
   ≡⟨ wd (op (⨅ I 𝒜) f) (λ s → ((⨅ I 𝒜) ⟦ t s ⟧) tup)(λ s j → (𝒜 j ⟦ t s ⟧)(λ ℓ → tup ℓ j)) (λ i → IH' i tup) ⟩
  (op (⨅ I 𝒜) f)(λ s j → (𝒜 j ⟦ t s ⟧) (λ ℓ → tup ℓ j)) ∎
   where
   IH' : ∀ i tup → (⨅ I 𝒜 ⟦ t i ⟧) tup ≡ (λ j → (𝒜 j ⟦ t i ⟧) (λ ℓ → tup ℓ j))
   IH' i tup = interp-prod fe₀ (t i) 𝒜 tup


-- Compatibility of terms

comm-hom-term : swelldef β → {𝑨 : structure {α} 𝑅 {ρ₀} 𝐹} (𝑩 : structure {β} 𝑅 {ρ₁} 𝐹)
                (h : hom 𝑨 𝑩){X : Type χ}(t : Term X) (a : X → carrier 𝑨)
                -----------------------------------------
  →             ∣ h ∣ ((𝑨 ⟦ t ⟧) a) ≡ (𝑩 ⟦ t ⟧) (∣ h ∣ ∘ a)

comm-hom-term _ 𝑩 h (ℊ x) a = refl
comm-hom-term wd {𝑨} 𝑩 (h , hhom) (node 𝑓 𝑡) a =
 h ((op 𝑨 𝑓) λ i →  (𝑨 ⟦ 𝑡 i ⟧) a)    ≡⟨ snd hhom 𝑓 (λ x → (𝑨 ⟦ 𝑡 x ⟧) a)  ⟩
 (op 𝑩 𝑓)(λ i → h ((𝑨 ⟦ 𝑡 i ⟧) a))    ≡⟨ ξ ⟩
 (op 𝑩 𝑓)(λ r → (𝑩 ⟦ 𝑡 r ⟧) (h ∘ a))  ∎
 where
 IH : (i : arity 𝐹 𝑓) → h ((𝑨 ⟦ 𝑡 i ⟧) a) ≡ (𝑩 ⟦ 𝑡 i ⟧) (λ x → h (a x))
 IH i = comm-hom-term wd 𝑩 (h , hhom) (𝑡 i) a

 ξ : op 𝑩 𝑓 (λ i → h ((𝑨 ⟦ 𝑡 i ⟧) a)) ≡ op 𝑩 𝑓 (λ r → (𝑩 ⟦ 𝑡 r ⟧) (λ x → h (a x)))
 ξ = wd (op 𝑩 𝑓) (λ i → h ((𝑨 ⟦ 𝑡 i ⟧) a)) (λ r → (𝑩 ⟦ 𝑡 r ⟧) (h ∘ a)) IH

-- Theorem. Congruences are compatible with terms.

cong-term-compatibility : {X : Type χ}{𝑨 : structure {α} 𝑅 {ρ₀} 𝐹}(t : Term X)(θ : con 𝑨)
 →                        (𝑨 ⟦ t ⟧) |: fst ∣ θ ∣
cong-term-compatibility (ℊ x) θ p = p x
cong-term-compatibility (node 𝑓 𝑡) θ p = snd θ 𝑓 (λ i → cong-term-compatibility (𝑡 i) θ p)

-- alias (shorthand notation for cong-term-compatibility)
_∥:_ : {X : Type χ}{𝑨 : structure {α} 𝑅 {ρ₀} 𝐹}(t : Term X)(θ : con 𝑨) → (𝑨 ⟦ t ⟧) |: fst ∣ θ ∣
t ∥: θ = cong-term-compatibility t θ

-- Term equivalence
-- module _ {X : Type χ}{𝑨 : structure {α} 𝑅 {ρ₀} 𝐹}{𝑩 : structure {β} 𝑅 {ρ₁} 𝐹} where


\end{code}


--------------------------------------



















<!-- For the sake of comparison, here is the analogous theorem using `compatible-fun`.

--   compatible-term : {𝑨 : structure {α} 𝑅 {ρ₀} 𝐹}(t : Term X)(θ : Con{𝓦} 𝑨) → compatible-op (𝑨 ⟦ t ⟧) ∣ θ ∣
--   compatible-term (ℊ x) θ p = λ y z → z x
--   compatible-term (node 𝑓 𝑡) θ u v p = (is-compatible ∥ θ ∥) 𝑓 λ x → ((compatible-op (𝑡 x) θ) u v) p
-->
-- Imports from Agda (builtin/primitive) and the Agda Standard Library
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Data.Product using (_,_; Σ; _×_)
open import Function.Base  using (_∘_)
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality.Core using (cong; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Unary using (Pred)

-- Imports from the Agda Universal Algebra Library
open import Overture.Inverses using (IsSurjective; Image_∋_; Inv; InvIsInv; eq)
open import Overture.Preliminaries
 using (Type; 𝓞; 𝓤; 𝓥; 𝓦; χ; 𝓨; Π; -Π; -Σ; _∙_;_⁻¹; ∣_∣; ∥_∥)

open import Algebras.Basic
open import Relations.Discrete using (_|:_)

