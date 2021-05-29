---
layout: default
title : structures.Congruences module (cubical-structures library)
date : 2021-05-12
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

open import structures.base

module structures.Congruences {𝑅 𝐹 : Signature} where

open import agda-imports
open import overture.preliminaries
open import relations.discrete
open import relations.extensionality
open import relations.quotients

private variable α ρ : Level

Con : (𝑨 : Structure α 𝑅 ρ 𝐹) → Type (lsuc ℓ₀ ⊔ α)
Con 𝑨 = Σ[ θ ∈ Equivalence ∣ 𝑨 ∣ ] (Compatible 𝑨 ∣ θ ∣)

record IsMinBin {A : Type α} (_≣_ : BinRel A ℓ₀ ) : Typeω where -- (α ⊔ ρ) where
 field
   isequiv : IsEquivalence{α}{ℓ₀} _≣_
   ismin : {ρ' : Level}(_≋_ : BinRel A ρ'){x y : A} → x ≣ y → x ≋ y

 reflexive : _≡_ ⇒ _≣_
 reflexive refl = IsEquivalence.refl isequiv

 corefl : _≣_ ⇒ _≡_
 corefl x≣y = ismin _≡_ x≣y


-- 𝟎 : (A : Type α) → BinRel A α
-- 𝟎 A = _≡_

𝟎-IsEquivalence : {A : Type α} →  IsEquivalence{α}{α}{A = A} _≡_
𝟎-IsEquivalence = record { refl = refl ; sym = sym ; trans = trans }

-- 𝟎-Equivalence : {A : Type α} → Equivalence{α} A
-- 𝟎-Equivalence {A = A} = 𝟎 A , 𝟎-IsEquivalence


module _ {α ρ : Level} {𝑨 : Structure α 𝑅 ρ 𝐹} where

 open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)

 𝟎-compatible-op : swelldef α → (𝑓 : ∣ 𝐹 ∣) → (𝑓 ᵒ 𝑨) |: _≡_
 𝟎-compatible-op wd 𝑓 {i}{j} ptws0  = γ
  where
  γ : (𝑓 ᵒ 𝑨) i ≡ (𝑓 ᵒ 𝑨) j
  γ = wd (𝑓 ᵒ 𝑨) i j ptws0 -- (fe ptws0) -- cong (𝑓 ᵒ 𝑨) (fe ptws0)

 𝟎-compatible : swelldef α → Compatible 𝑨 _≡_
 𝟎-compatible wd 𝑓 x = 𝟎-compatible-op wd 𝑓 x

 𝟎-comp→𝟎-lift-comp' : {ρ : Level} → swelldef (α ⊔ ρ) → Compatible 𝑨 _≡_ → Compatible (Lift-struc 𝑨 ρ) _≡_
 𝟎-comp→𝟎-lift-comp' {ρ = ρ} wd compA 𝑓 {u}{v} uv = goal
  where
  goal : (𝑓 ᵒ Lift-struc 𝑨 ρ) u ≡ (𝑓 ᵒ Lift-struc 𝑨 ρ) v
  goal = wd (𝑓 ᵒ Lift-struc 𝑨 ρ) u v uv

 𝟎-compatible-op' : swelldef α → (𝑓 : ∣ 𝐹 ∣) → compatible-op (𝑓 ᵒ 𝑨) _≡_
 𝟎-compatible-op' wd 𝑓 u v uv = wd (𝑓 ᵒ 𝑨) u v uv

 -- 𝟘 : {ρ : Level} → swelldef α → swelldef (α ⊔ ρ) → Con{ α ⊔ ρ }{ β } (Lift-struc 𝑨 ρ)
 -- 𝟘 {ρ = ρ} wd0 wd = 𝟎-Equivalence , goal
 --  where
 --  goal : compatible (Lift-struc 𝑨 ρ) (𝟎 ∣ Lift-struc 𝑨 ρ ∣)
 --  goal 𝑓 {u}{v} uv = 𝟎-comp→𝟎-lift-comp' wd (𝟎-compatible-op' wd0) 𝑓 u v uv


\end{code}


A concrete example is `⟪𝟎⟫[ 𝑨 ╱ θ ]`, presented in the next subsection.

#### <a id="quotient-algebras">Quotient algebras</a>

\begin{code}

module _ {α : Level} where


 _╱_ : (𝑨 : Structure α 𝑅 ℓ₀ 𝐹) → Con 𝑨 → Structure (α ⊔ ℓ₁) 𝑅 ℓ₀ 𝐹

 𝑨 ╱ θ = (∣ 𝑨 ∣ / ∣ θ ∣)                                    -- domain of the quotient algebra
         , (λ r x → (r ʳ 𝑨) λ i → ⌞ x i ⌟)
         , λ f b → ⟪ (f ᵒ 𝑨) (λ i → ⌞ b i ⌟) / ∣ θ ∣ ⟫
\end{code}

The (infered) types of the arguments of the relation (resp., operation) interpretations are `r : ∣ 𝑅 ∣`  and `x : ∥ 𝑅 ∥ r → ∣ 𝑨 ∣ / ∣ θ ∣` (resp., `f : ∣ 𝐹 ∣`  and `b : ∥ 𝐹 ∥ f → ∣ 𝑨 ∣ / ∣ θ ∣`).

Finally, the following elimination rule is sometimes useful.

\begin{code}

 /≡-elim : {𝑨 : Structure α 𝑅 ℓ₀ 𝐹}( (θ , _ ) : Con 𝑨){u v : ∣ 𝑨 ∣}
  →    ⟪ u / θ ⟫ ≡ ⟪ v / θ ⟫ → ∣ θ ∣ u v
 /≡-elim θ {u}{v} x =  ⟪⟫≡-elim u v x

\end{code}


**Example**. If we adopt the notation `𝟎[ 𝑨 ╱ θ ]` for the zero (or identity) relation on the quotient algebra `𝑨 ╱ θ`, then we define the zero relation as follows.

\begin{code}

module _ {α : Level} where

 𝟘[_╱_] : (𝑨 : Structure α 𝑅 ℓ₀ 𝐹)(θ : Con 𝑨) → BinRel (∣ 𝑨 ∣ / ∣ θ ∣) (lsuc ℓ₀ ⊔ α)
 𝟘[ 𝑨 ╱ θ ] = λ u v → u ≡ v

\end{code}

From this we easily obtain the zero congruence of `𝑨 ╱ θ` by applying the `Δ` function defined above.
\begin{code}

--  open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
-- 𝟎-Equivalence : {A : Type α} → Equivalence{α} A
-- 𝟎-Equivalence {A = A} = 𝟎 A , 𝟎-IsEquivalence

-- module _ {α ρ : Level} {A : Type α} where


-- module _ {α ρ : Level}{wd : swelldef α}{wd' : swelldef ρ}  where

 -- 𝟎[_╱_] : (𝑨 : Structure 𝑅 𝐹)(θ : Con 𝑨) → Con (𝑨 ╱ θ)
 -- 𝟎[ 𝑨 ╱ θ ] = ( R , Reqiv) , {!!}
 --  where
 --  R : BinRel ∣ 𝑨 ╱ θ ∣ ρ
 --  R (x₁ , x₂) (y₁ , y₂) = x₁ ⊆ y₁ × y₁ ⊆ x₁
 --  Reqiv : IsEquivalence R
 --  Reqiv = record { refl = (λ z → z) , (λ z → z) ; sym = λ Rxy → snd Rxy , fst Rxy ; trans = λ Rij Rjk → (⊑-trans {!!} {!!} {!!} {!!}) , (⊑-trans fst {!!} {!!} {!!}) }
 --  goal : compatible (𝑨 ╱ θ) ∣ {!!} , {!!} ∣ -- compatible (Lift-struc 𝑨 {!!}) (𝟎 ∣ Lift-struc 𝑨 {!!} ∣)
 --  goal 𝑓 {u}{v} uv = {!!} -- 𝟎-comp→𝟎-lift-comp' wd (𝟎-compatible-op' wd) 𝑓 u v uv
-- ⊆-trans : Transitive (_⊆_ {A = A} {ℓ})
-- ⊆-trans P⊆Q Q⊆R x∈P = Q⊆R (P⊆Q x∈P)

 -- 𝟘 : funext ℓ₀ α → Con 𝑨
 -- 𝟘 fe = 𝟎-Equivalence , 𝟎-compatible fe --   IsCongruence→Con 𝟎 Δ
-- 𝑨 ╱ θ : Structure 𝑅 𝐹 {α ⊔ lsuc ρ}{ρ}
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

