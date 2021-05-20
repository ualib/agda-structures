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
generalize this to truly arbitrary arity types, but so far we haven't found a use-case
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
                  -- whether it's a real restriction---are there use-cases requiring
                  -- arities inhabiting higher types?

-- Relations of arbitrary arity over a single sort.
Rel : Arity → Type α → (β : Level) → Type (α ⊔ lsuc β)
Rel ar A β = (ar → A) → Type β

-- Multisorted relations of arbitrary arity
REL : (arity : Arity) → (arity → Type α) → (β : Level) → Type (α ⊔ lsuc β)
REL arity 𝒜 β = ((i : arity) → 𝒜 i) → Type β

-- Compatibility of relations and operations.
module _ {I J : Arity} {A : Type α} where

 -- Lift a relation of tuples up to a relation on tuples of tuples.
 evalRel : Rel I A β → (I → J → A) → Type β
 evalRel R t = ∀ (j : J) → R λ i → t i j

 {- A relation R is compatible with an operation 𝑓 if for every tuple t of tuples
    belonging to R, the tuple whose elements are the result of applying 𝑓 to
    sections of t also belongs to R. (see the bottom of this file for an heuristic explanation) -}
 compRel : Op J A → Rel I A β → Type (α ⊔ β)
 compRel 𝑓 R  = ∀ (t : (I → J → A)) → (evalRel R t → R λ i → (𝑓 (t i)))

module _ {I J : Arity} {𝒜 : I → Type α} where

 -- Lift a relation of tuples up to a relation on tuples of tuples.
 evalREL : REL I 𝒜 β → (∀ i → (J → 𝒜 i)) → Type β
 evalREL R t = ∀ j → R (λ i → (t i) j)

 compREL : (∀ i → Op J (𝒜 i)) → REL I 𝒜 β → Type (α ⊔ β)
 compREL 𝑓 R  = ∀ t → (evalREL R) t → R λ i → (𝑓 i)(t i)

\end{code}


### Heuristic description of `evalRel` and `compRel`.

The function `evalRel` "lifts" an `I`-ary relation to an `(I → J)`-ary relation. The lifted relation will relate an `I`-tuple of `J`-tuples when the "`I`-slices" (or "rows") of the `J`-tuples belong to the original relation. The second definition denotes compatibility of an operation with a continuous relation.

Readers who find the syntax of the last two definitions nauseating might be helped by an explication of the semantics of these deifnitions. First, internalize the fact that `t : I → J → A` denotes an `I`-tuple of `J`-tuples of inhabitants of `A`. Next, recall that a continuous relation `R` denotes a certain collection of `I`-tuples (if `x : I → A`, then `R x` asserts that `x` "belongs to" or "satisfies" `R`).  For such `R`, the type `evalRel R` represents a certain collection of `I`-tuples of `J`-tuples, namely, the tuples `t : I → J → A` for which `evalRel R t` holds.

For simplicity, pretend for a moment that `J` is a finite set, say, `{1, 2, ..., J}`, so that we can write down a couple of the `J`-tuples as columns. For example, here are the i-th and k-th columns (for some `i k : I`).

```
t i 1      t k 1
t i 2      t k 2  <-- (a row of I such columns forms an I-tuple)
  ⋮          ⋮
t i J      t k J
```

Now `evalRel R t` is defined by `∀ j → R (λ i → t i j)` which asserts that each row of the `I` columns shown above belongs to the original relation `R`. Finally, `compRel` takes a `J`-ary operation `𝑓 : Op J A` and an `I`-tuple `t : I → J → A` of `J`-tuples, and determines whether the `I`-tuple `λ i → 𝑓 (t i)` belongs to `R`.



-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

