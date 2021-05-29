---
layout: default
title : structures module
date : 2021-05-28
author: William DeMeo
---

This is the structures module which presents general (relational-algebraic) structures as inhabitants of record types.  For a similar development using Sigma types see the module called Structures (with an upper-case S).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module structures where

open import structures.base public
open import structures.congruences public
open import structures.products public

\end{code}

