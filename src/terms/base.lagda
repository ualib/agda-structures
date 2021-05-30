---
layout: default
title : terms.base module
date : 2021-05-30
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import agda-imports
open import overture.preliminaries
open import overture.inverses
open import relations.continuous
open import structures.base

module terms.base {𝑅 𝐹 : signature} where

open import homs.base


private variable α ρ ρ₀ χ : Level

data Term (X : Type χ ) : Type χ where
 ℊ : X → Term X    -- (ℊ for "generator")
 node : (f : symbol 𝐹)(t : arity 𝐹 f → Term X) → Term X

open Term public


𝑻 : (X : Type χ ) → structure {χ} 𝑅 {ℓ₀} 𝐹
𝑻 X = record { carrier = Term X
             ; rel = λ 𝑟 x → ⊥  -- each relation interpreted in the free structure is empty
             ; op = node
             }

private variable X : Type χ

free-lift : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹)(h : X → carrier 𝑨) → carrier (𝑻 X) → carrier 𝑨
free-lift _ h (ℊ x) = h x
free-lift 𝑨 h (node f 𝑡) = (op 𝑨 f) (λ i → free-lift 𝑨 h (𝑡 i))

free-unique : funext ℓ₀ α → (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹)(g h : hom (𝑻 X) 𝑨)
 →            (∀ x → ∣ g ∣ (ℊ x) ≡ ∣ h ∣ (ℊ x))
              ----------------------------------------
 →            ∀ (t : Term X) →  ∣ g ∣ t ≡ ∣ h ∣ t

free-unique _ _ _ _ p (ℊ x) = p x
free-unique fe 𝑨 (g , grh , goh )(h , hrh , hoh) p (node 𝑓 𝑡) =
 g (node 𝑓 𝑡)     ≡⟨ goh 𝑓 𝑡 ⟩
 (op 𝑨 𝑓)(g ∘ 𝑡)  ≡⟨ ν ⟩
 (op 𝑨 𝑓)(h ∘ 𝑡)  ≡⟨ (hoh 𝑓 𝑡)⁻¹ ⟩
 h (node 𝑓 𝑡)     ∎
 where
 ν : (op 𝑨 𝑓) (g ∘ 𝑡) ≡ (op 𝑨 𝑓) (h ∘ 𝑡)
 ν = cong (op 𝑨 𝑓) (fe λ i → free-unique fe 𝑨 (g , grh , goh) (h , hrh , hoh) p (𝑡 i))

lift-hom : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹) → (X → carrier 𝑨) → hom (𝑻 X) 𝑨
lift-hom 𝑨 h = free-lift 𝑨 h , (λ R a ()) , λ f a → cong (op 𝑨 f) refl

\end{code}

Let's account for what we have proved thus far about the term algebra.  If we postulate a type `X : Type 𝓧` (representing an arbitrary collection of variable symbols) such that for each `𝑆`-algebra `𝑨` there is a map from `X` to the domain of `𝑨`, then it follows that for every `𝑆`-algebra `𝑨` there is a homomorphism from `𝑻 X` to `∣ 𝑨 ∣` that "agrees with the original map on `X`," by which we mean that for all `x : X` the lift evaluated at `ℊ x` is equal to the original function evaluated at `x`.

If we further assume that each of the mappings from `X` to `∣ 𝑨 ∣` is *surjective*, then the homomorphisms constructed with `free-lift` and `lift-hom` are *epimorphisms*, as we now prove.

\begin{code}

lift-of-epi-is-epi : (𝑨 : structure {α} 𝑅 {ρ₀} 𝐹){h₀ : X → carrier 𝑨}
 →                   IsSurjective h₀ → IsSurjective ∣ lift-hom 𝑨 h₀ ∣
lift-of-epi-is-epi 𝑨 {h₀} hE y = γ
 where
 h₀⁻¹y = Inv h₀ (hE y)

 η : y ≡ ∣ lift-hom 𝑨 h₀ ∣ (ℊ h₀⁻¹y)
 η = (InvIsInv h₀ (hE y))⁻¹

 γ : Image ∣ lift-hom 𝑨 h₀ ∣ ∋ y
 γ = eq (ℊ h₀⁻¹y) η

\end{code}

The `lift-hom` and `lift-of-epi-is-epi` types will be called to action when such epimorphisms are needed later (e.g., in the [Varieties][] module).
