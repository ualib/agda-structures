---
layout: default
title : sturctures.products module (cubical-structures library)
date : 2021-05-11
author: William DeMeo
---

### Product structures

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

-- open import Agda.Primitive using (_⊔_; lsuc)
-- open import Relation.Unary using (Pred; _∈_)

-- open import Cubical.Core.Primitives using (_≡_; Type; Level; Σ-syntax;  i0; i1; fst; snd; _,_)
-- open import Cubical.Foundations.Prelude using (refl; sym; _∙_; funExt; cong; _∎; _≡⟨_⟩_)
-- open import Cubical.Foundations.Function using (_∘_)
-- open import Cubical.Data.Sigma.Base using (_×_)

-- -- Imports from the Agda Universal Algebra Library
-- open import overture.preliminaries using (Π; Π-syntax; _⁻¹; id; ∣_∣)
-- open import structures.basic using (Signature; Structure; _ʳ_; _ᵒ_; signature; structure)
-- open import overture.inverses using (IsInjective; IsSurjective)
-- open import relations.discrete using (ker)


module structures.products  where

open import agda-imports
open import structures.base
open import overture.preliminaries
open import relations.continuous


variable
 ι : Level

module _ {𝑅 𝐹 : Signature} where

 ⨅ : (ℑ : Type ι)(ℬ : ℑ → Structure 𝑅 𝐹 {β}) → Structure 𝑅 𝐹
 ⨅ ℑ ℬ = Π[ 𝔦 ∈ ℑ ] ∣ ℬ 𝔦 ∣ ,                     -- domain of the product structure
          ( λ r 𝑎 → ∀ 𝔦 → (r ʳ ℬ 𝔦) λ x → 𝑎 x 𝔦 ) , -- interpretations of relations
          ( λ 𝑓 𝑎 𝔦 → (𝑓 ᵒ ℬ 𝔦) λ x → 𝑎 x 𝔦 )        -- interpretations of  operations

module _ {𝑅 𝐹 : Signature}{𝒦 : Pred (Structure 𝑅 𝐹 {β}) (lsuc β)} where

 ℑ : Type (lsuc β)
 ℑ = Σ[ 𝑨 ∈ Structure 𝑅 𝐹 ] 𝑨 ∈ 𝒦

 𝔄 : ℑ → Structure 𝑅 𝐹
 𝔄 𝔦 = ∣ 𝔦 ∣

 class-prod : Structure  𝑅 𝐹
 class-prod = ⨅ ℑ 𝔄

\end{code}

If `p : 𝑨 ∈ 𝒦`, we view the pair `(𝑨 , p) ∈ ℑ` as an *index* over the class, so we can think of `𝔄 (𝑨 , p)` (which is simply `𝑨`) as the projection of the product `⨅ 𝔄` onto the `(𝑨 , p)`-th component.


#### Representing structures with record types

\begin{code}

module _ {𝑅 𝐹 : signature} where
 open structure

 ⨅' : (ℑ : Type ι)(ℬ : ℑ → structure 𝑅 𝐹 {β}) → structure 𝑅 𝐹
 ⨅' ℑ ℬ = record
           { univ = Π[ 𝔦 ∈ ℑ ] univ (ℬ 𝔦)                      -- domain of the product structure
           ; srel = λ r a → ∀ i → (srel (ℬ i) r)(λ x → a x i) -- interpretations of relations
           ; sop  = λ f a i → (sop (ℬ i) f) (λ x → a x i)     -- interpretations of operations
           }

module _ {𝑅 𝐹 : signature} {𝒦 : Pred (structure 𝑅 𝐹 {β}) (lsuc β)} where

  ℑ' : Type (lsuc β)
  ℑ' = Σ[ 𝑨 ∈ structure 𝑅 𝐹 ] 𝑨 ∈ 𝒦

  𝔄' : ℑ' → structure 𝑅 𝐹
  𝔄' 𝔦 = ∣ 𝔦 ∣

  class-prod' : structure 𝑅 𝐹
  class-prod' = ⨅' ℑ' 𝔄'

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

















-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Unary using (Pred; _∈_)

-- Imports from the Agda Universal Algebra Library
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; _≡⟨_⟩_; _∎; _⁻¹; 𝑖𝑑; ∣_∣; ∥_∥)
-- open import Algebras.Basic


-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Binary.PropositionalEquality.Core using (trans)

