---
layout: title-page
title : the agda-structures library
date : 2021-05-20
author: William DeMeo
---

Make sure your $HOME/.agda/libraries file contains lines similar to the following (depending on where you installed the Agda Standard Library).

```
~/opt/AGDA/agda-stdlib-1.6/standard-library.agda-lib
```

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module agda-structures where

open import overture
open import relations
open import structures
open import homs

\end{code}

--------------------------

