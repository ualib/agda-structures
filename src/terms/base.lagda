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

module terms.base {๐ ๐น : signature} where

open import homs.base


private variable ฮฑ ฯ ฯโ ฯ : Level

data Term (X : Type ฯ ) : Type ฯ where
 โ : X โ Term X    -- (โ for "generator")
 node : (f : symbol ๐น)(t : arity ๐น f โ Term X) โ Term X

open Term public


๐ป : (X : Type ฯ ) โ structure {ฯ} ๐ {โโ} ๐น
๐ป X = record { carrier = Term X
             ; rel = ฮป ๐ x โ โฅ  -- each relation interpreted in the free structure is empty
             ; op = node
             }

private variable X : Type ฯ

free-lift : (๐จ : structure {ฮฑ} ๐ {ฯโ} ๐น)(h : X โ carrier ๐จ) โ carrier (๐ป X) โ carrier ๐จ
free-lift _ h (โ x) = h x
free-lift ๐จ h (node f ๐ก) = (op ๐จ f) (ฮป i โ free-lift ๐จ h (๐ก i))

free-unique : funext โโ ฮฑ โ (๐จ : structure {ฮฑ} ๐ {ฯโ} ๐น)(g h : hom (๐ป X) ๐จ)
 โ            (โ x โ โฃ g โฃ (โ x) โก โฃ h โฃ (โ x))
              ----------------------------------------
 โ            โ (t : Term X) โ  โฃ g โฃ t โก โฃ h โฃ t

free-unique _ _ _ _ p (โ x) = p x
free-unique fe ๐จ (g , grh , goh )(h , hrh , hoh) p (node ๐ ๐ก) =
 g (node ๐ ๐ก)     โกโจ goh ๐ ๐ก โฉ
 (op ๐จ ๐)(g โ ๐ก)  โกโจ ฮฝ โฉ
 (op ๐จ ๐)(h โ ๐ก)  โกโจ (hoh ๐ ๐ก)โปยน โฉ
 h (node ๐ ๐ก)     โ
 where
 ฮฝ : (op ๐จ ๐) (g โ ๐ก) โก (op ๐จ ๐) (h โ ๐ก)
 ฮฝ = cong (op ๐จ ๐) (fe ฮป i โ free-unique fe ๐จ (g , grh , goh) (h , hrh , hoh) p (๐ก i))

lift-hom : (๐จ : structure {ฮฑ} ๐ {ฯโ} ๐น) โ (X โ carrier ๐จ) โ hom (๐ป X) ๐จ
lift-hom ๐จ h = free-lift ๐จ h , (ฮป R a ()) , ฮป f a โ cong (op ๐จ f) refl

\end{code}

Let's account for what we have proved thus far about the term algebra.  If we postulate a type `X : Type ๐ง` (representing an arbitrary collection of variable symbols) such that for each `๐`-algebra `๐จ` there is a map from `X` to the domain of `๐จ`, then it follows that for every `๐`-algebra `๐จ` there is a homomorphism from `๐ป X` to `โฃ ๐จ โฃ` that "agrees with the original map on `X`," by which we mean that for all `x : X` the lift evaluated at `โ x` is equal to the original function evaluated at `x`.

If we further assume that each of the mappings from `X` to `โฃ ๐จ โฃ` is *surjective*, then the homomorphisms constructed with `free-lift` and `lift-hom` are *epimorphisms*, as we now prove.

\begin{code}

lift-of-epi-is-epi : (๐จ : structure {ฮฑ} ๐ {ฯโ} ๐น){hโ : X โ carrier ๐จ}
 โ                   IsSurjective hโ โ IsSurjective โฃ lift-hom ๐จ hโ โฃ
lift-of-epi-is-epi ๐จ {hโ} hE y = ฮณ
 where
 hโโปยนy = Inv hโ (hE y)

 ฮท : y โก โฃ lift-hom ๐จ hโ โฃ (โ hโโปยนy)
 ฮท = (InvIsInv hโ (hE y))โปยน

 ฮณ : Image โฃ lift-hom ๐จ hโ โฃ โ y
 ฮณ = eq (โ hโโปยนy) ฮท

\end{code}

The `lift-hom` and `lift-of-epi-is-epi` types will be called to action when such epimorphisms are needed later (e.g., in the [Varieties][] module).
