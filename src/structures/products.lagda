---
layout: default
title : sturctures.products module (cubical-structures library)
date : 2021-05-11
author: William DeMeo
---

### Product structures

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

open import structures.base

module structures.products {๐ ๐น : signature} where

open import agda-imports
open import overture.preliminaries
open import relations.continuous


module _ {ฮฑ ฯ ฮน : Level} where

 โจ : (โ : Type ฮน)(๐ : โ โ structure {ฮฑ} ๐ {ฯ} ๐น) โ structure {ฮฑ โ ฮน} ๐ {ฯ โ ฮน} ๐น
 โจ โ ๐ = record { carrier = ฮ [ ๐ฆ โ โ ] carrier (๐ ๐ฆ)            -- domain of the product structure
                 ; rel = ฮป r a โ โ ๐ฆ โ (rel (๐ ๐ฆ) r) ฮป x โ a x ๐ฆ -- interpretation of relations
                 ; op = ฮป ๐ a ๐ฆ โ (op (๐ ๐ฆ) ๐) ฮป x โ a x ๐ฆ       -- interpretation of  operations
                 }


module _ {ฮฑ ฯ ฯ : Level} {๐ฆ : Pred (structure {ฮฑ} ๐ {ฯ} ๐น) ฯ} where

 โp : Level
 โp = lsuc (ฮฑ โ ฯ) โ ฯ

 โ : Type โp
 โ = ฮฃ[ ๐จ โ structure {ฮฑ} ๐ {ฯ} ๐น ] ๐จ โ ๐ฆ

 ๐ : โ โ structure {ฮฑ} ๐ {ฯ} ๐น
 ๐ ๐ฆ = โฃ ๐ฆ โฃ

 class-product : structure ๐ ๐น
 class-product = โจ โ ๐

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

















-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; ฮฃ; _ร_)
-- open import Relation.Unary using (Pred; _โ_)

-- Imports from the Agda Universal Algebra Library
-- open import Overture.Preliminaries using (Type; ๐; ๐; ๐ค; ๐ฅ; ๐ฆ; ฮ ; -ฮ ; -ฮฃ; _โกโจ_โฉ_; _โ; _โปยน; ๐๐; โฃ_โฃ; โฅ_โฅ)
-- open import Algebras.Basic


-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Binary.PropositionalEquality.Core using (trans)

-- open import Agda.Primitive using (_โ_; lsuc)
-- open import Relation.Unary using (Pred; _โ_)

-- open import Cubical.Core.Primitives using (_โก_; Type; Level; ฮฃ-syntax;  i0; i1; fst; snd; _,_)
-- open import Cubical.Foundations.Prelude using (refl; sym; _โ_; funExt; cong; _โ; _โกโจ_โฉ_)
-- open import Cubical.Foundations.Function using (_โ_)
-- open import Cubical.Data.Sigma.Base using (_ร_)

-- -- Imports from the Agda Universal Algebra Library
-- open import overture.preliminaries using (ฮ ; ฮ -syntax; _โปยน; id; โฃ_โฃ)
-- open import structures.basic using (Signature; Structure; _สณ_; _แต_; signature; structure)
-- open import overture.inverses using (IsInjective; IsSurjective)
-- open import relations.discrete using (ker)


