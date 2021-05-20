---
layout: default
title : relations.continuous
date : 2021-05-20
author: William DeMeo
---

This module defines types for representing relations that are more general than the
standard relation types one finds, e.g., in the Agda standard library.  We generalize
in two stages.

First, we define the type `Rel` to represent relations of arbitrary arity over a single
sort (or type).  Inhabitants of the Rel type can be thought of heuristically as subsets
of cartesian powers of a single set (where the power is not necessarily finite or even
countable).

Second, we define the type `REL` to represent relations of arbitrary arity over an
arbitrary family or sorts.  Inhabitants of the REL type can be thought of heuristically
as subsets of cartesian products of an arbitrary (not necessarily enumerable) family of
sets.

The arities of the relations inhabiting the types Rel and REL are "arbitrary" insofar as
the arities live in arbitrary types *at universe level zero*. This restriction is not a
real limitation and is only a choice we made for notational convenience.  We could easily
generalize this to truly arbitrary arity types, but so far we haven't found a use case
requiring such generality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module relations.continuous where

open import agda-imports
open import overture.preliminaries
open import relations.discrete using (Op)

ℓ₀ ℓ₁ : Level  -- (alias)
ℓ₀ = lzero
ℓ₁ = lsuc ℓ₀

Arity : Type ℓ₁
Arity = Type ℓ₀   -- Assuming for now that all arity types have universe level 0.
                  -- This is merely for notational convenience, and it's not clear
                  -- whether it's a real restriction---are there use cases requiring
                  -- arities inhabiting higher types?

-- Relations of arbitrary arity over a single sort.
Rel : Arity → Type α → (β : Level) → Type (α ⊔ lsuc β)
Rel ar A β = (ar → A) → Type β

-- Multisorted relations of arbitrary arity
REL : (arity : Arity) → (arity → Type α) → (β : Level) → Type (α ⊔ lsuc β)
REL arity 𝒜 β = ((i : arity) → 𝒜 i) → Type β





module _ {I J : Arity} {A : Type α} where

 eval-cont-rel : Rel I A β → (I → J → A) → Type β
 eval-cont-rel R a = ∀ (j : J) → R λ i → a i j

 cont-compatible-op : Op J A → Rel I A β → Type (α ⊔ β)
 cont-compatible-op 𝑓 R  = ∀ (a : (I → J → A)) → (eval-cont-rel R a → R λ i → (𝑓 (a i)))

module _ {I J : Arity} {𝒜 : I → Type α} where

 eval-dep-rel : REL I 𝒜 β → (∀ i → (J → 𝒜 i)) → Type β
 eval-dep-rel R a = ∀ j → R (λ i → (a i) j)

 dep-compatible-op : (∀ i → Op J (𝒜 i)) → REL I 𝒜 β → Type (α ⊔ β)
 dep-compatible-op 𝑓 R  = ∀ a → (eval-dep-rel R) a → R λ i → (𝑓 i)(a i)

\end{code}








-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

