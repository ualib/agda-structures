---
layout: default
title : Structures module
date : 2021-05-28
author: William DeMeo
---

This is the Structures module which presents general (relational-algebraic) structures as inhabitants of Sigma types.  For a similar development using record types see the module called structures (with a lower-case s).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Structures where

open import Structures.Base public
open import Structures.Congruences public
open import Structures.Products public

\end{code}

