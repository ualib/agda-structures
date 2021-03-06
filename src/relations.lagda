---
layout: default
title : relations module
date : 2021-05-20
author: William DeMeo
---

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-} -- --cubical #-}

module relations where

open import relations.discrete public
open import relations.continuous public
open import relations.quotients public
open import relations.truncation public
-- open import Relations.Extensionality public

\end{code}


-------------------------------------

{% include UALib.Links.md %}
