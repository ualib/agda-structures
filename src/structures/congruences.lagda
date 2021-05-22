---
layout: default
title : structures.congruences module (cubical-structures library)
date : 2021-05-12
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

open import structures.base

module structures.congruences {𝑅 𝐹 : Signature} where

open import agda-imports
open import overture.preliminaries
open import relations.discrete
open import relations.quotients



Con : {ρ α β : Level}(𝑩 : Structure{α} 𝑅 𝐹 {β}) → Type (lsuc ρ ⊔ β)
Con {ρ} 𝑩 = Σ[ θ ∈ Equivalence{ρ} ∣ 𝑩 ∣ ] (compatible 𝑩 ∣ θ ∣)

𝟎-IsEquivalence : {B : Type β} →  IsEquivalence {A = B} 𝟎
𝟎-IsEquivalence = record { refl = refl ; sym = λ x → sym x ; trans = λ x x₁ → trans x x₁ }

𝟎-Equivalence : {B : Type β} → Equivalence {β} B
𝟎-Equivalence = 𝟎 , 𝟎-IsEquivalence


module _ {𝑩 : Structure{α} 𝑅 𝐹 {β}} where

 open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)

 𝟎-compatible-op : funext ℓ₀ β → (𝑓 : ∣ 𝐹 ∣) → (𝑓 ᵒ 𝑩) |: 𝟎
 𝟎-compatible-op fe 𝑓 {i}{j} ptws0  = γ -- cong (𝑓 ᵒ 𝑩) {!!}
  where
  γ : (𝑓 ᵒ 𝑩) i ≡ (𝑓 ᵒ 𝑩) j
  γ = cong (𝑓 ᵒ 𝑩) (fe ptws0)

 𝟎-compatible : funext ℓ₀ β → compatible 𝑩 𝟎
 𝟎-compatible fe = λ 𝑓 x → 𝟎-compatible-op fe 𝑓 x

 𝟘 : funext ℓ₀ β → Con 𝑩
 𝟘 fe = 𝟎-Equivalence , 𝟎-compatible fe --   IsCongruence→Con 𝟎 Δ


\end{code}


A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

#### <a id="quotient-algebras">Quotient algebras</a>

\begin{code}

module _ {α β : Level} where



 _╱_ : (𝑩 : Structure{α} 𝑅 𝐹 {β}) → Con{α} 𝑩 → Structure{α} 𝑅 𝐹 {lsuc α ⊔ β}

 𝑩 ╱ θ = (∣ 𝑩 ∣ / ∣ θ ∣)                                    -- domain of the quotient algebra
         , (λ r x → (r ʳ 𝑩) λ i → ⌞ x i ⌟)
         , λ f b → ⟪ (f ᵒ 𝑩) (λ i → ⌞ b i ⌟) / ∣ θ ∣ ⟫
\end{code}

The (infered) types of the arguments of the relation (resp., operation) interpretations are `r : ∣ 𝑅 ∣`  and `x : ∥ 𝑅 ∥ r → ∣ 𝑩 ∣ / ∣ θ ∣` (resp., `f : ∣ 𝐹 ∣`  and `b : ∥ 𝐹 ∥ f → ∣ 𝑩 ∣ / ∣ θ ∣`).


**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.

\begin{code}

 𝟘[_╱_] : (𝑩 : Structure{α} 𝑅 𝐹 {β})(θ : Con{α} 𝑩) → BinRel (∣ 𝑩 ∣ / ∣ θ ∣) (lsuc α ⊔ β)
 𝟘[ 𝑩 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.
\begin{code}

 open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)

 𝟎[_╱_] : (𝑩 : Structure{α} 𝑅 𝐹 {β})(θ : Con 𝑩){fe : funext ℓ₀ (lsuc α ⊔ β)} → Con{lsuc α ⊔ β} (𝑩 ╱ θ)
 𝟎[ 𝑩 ╱ θ ] {fe} =  𝟘{𝑩 = 𝑩 ╱ θ} fe

\end{code}


Finally, the following elimination rule is sometimes useful.

\begin{code}

 /≡-elim : {𝑩 : Structure{α} 𝑅 𝐹 {β}}( (θ , _ ) : Con{α} 𝑩){u v : ∣ 𝑩 ∣}
  →    ⟪ u / θ ⟫ ≡ ⟪ v / θ ⟫ → ∣ θ ∣ u v
 /≡-elim θ {u}{v} x =  ⟪⟫≡-elim u v x

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

















<!-- NO LONGER NEEDED ----------------------------------------------------------

-- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Agda.Builtin.Equality using (_≡_; refl)
-- open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
-- open import Level renaming (suc to lsuc; zero to lzero)
-- open import Data.Product using (_,_; Σ; _×_)
-- open import Relation.Binary using (Rel; IsEquivalence)
-- open import Relation.Unary using (Pred; _∈_)
-- open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)

-- -- Imports from the Agda Universal Algebra Library
-- open import Algebras.Basic
-- open import Overture.Preliminaries using (Type; 𝓘; 𝓞; 𝓤; 𝓥; 𝓦; Π; -Π; -Σ; ∣_∣; ∥_∥; fst)
-- open import Relations.Discrete using (𝟎; _|:_)
-- open import Relations.Quotients using (_/_; ⟪_⟫)

--------------------------------------------------------------------------------- -->
open _/ₜ_

_╱ₜ_ : (𝑩 : Structure 𝑅 𝐹 {β}) → Con{α} 𝑩 → Structure 𝑅 𝐹

𝑩 ╱ₜ θ = (∣ 𝑩 ∣ /ₜ ∣ fst θ ∣)                                    -- domain of the quotient algebra
, rel -- basic relations of the quotient structure
, op        -- basic operations of the quotient algebra
where
rel : (r : ∣ 𝑅 ∣)(b : ∥ 𝑅 ∥ r → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣) → Type ?
rel r b = ?
-- (λ 𝑟 [ x ] → ((𝑟 ʳ 𝑩) λ i → ∣ fst θ ∣ (x i)))
op : (f : ∣ 𝐹 ∣)(b : ∥ 𝐹 ∥ f → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣) → ∣ 𝑩 ∣ /ₜ ∣ fst θ ∣
op f b = ? -- λ 𝑓 [ 𝑎 ] → [ ((𝑓 ᵒ 𝑩)(λ i →  𝑎 i)) ]  

