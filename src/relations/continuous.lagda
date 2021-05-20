---
layout: default
title : relations.continuous
date : 2021-05-08
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- --cubical #-}

module relations.continuous where

open import overture.preliminaries
open import relations.discrete using (Op)


ContRel : Type γ → Type α → (β : Level) → Type(α ⊔ γ ⊔ lsuc β)
ContRel I A β = (I → A) → Type β

DepRel : (I : Type γ) → (I → Type α) → (β : Level) → Type(α ⊔ γ ⊔ lsuc β)
DepRel I 𝒜 β = ((i : I) → 𝒜 i) → Type β

module _ {I J : Type γ} {A : Type α} where

 eval-cont-rel : ContRel I A β → (I → J → A) → Type(γ ⊔ β)
 eval-cont-rel R a = ∀ (j : J) → R λ i → a i j

 cont-compatible-op : Op J A → ContRel I A β → Type(γ ⊔ α ⊔ β)
 cont-compatible-op 𝑓 R  = ∀ (a : (I → J → A)) → (eval-cont-rel R a → R λ i → (𝑓 (a i)))

module _ {I J : Type γ} {𝒜 : I → Type α} where

 eval-dep-rel : DepRel I 𝒜 β → (∀ i → (J → 𝒜 i)) → Type(γ ⊔ β)
 eval-dep-rel R a = ∀ j → R (λ i → (a i) j)

 dep-compatible-op : (∀ i → Op J (𝒜 i)) → DepRel I 𝒜 β → Type(γ ⊔ α ⊔ β)
 dep-compatible-op 𝑓 R  = ∀ a → (eval-dep-rel R) a → R λ i → (𝑓 i)(a i)

\end{code}








-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

