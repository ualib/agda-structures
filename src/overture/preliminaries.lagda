---
layout: default
title : overture.preliminaries module
date : 2021-05-20
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} --  --cubical #-}

module overture.preliminaries where

open import agda-imports
open import Relation.Binary.PropositionalEquality using (sym; trans)

private variable
 α β ρ : Level

{-Pi types. The dependent function type is traditionally denoted with a Pi symbol
  typically arranged as Π(x : A) B x, or something similar.  In Agda syntax, one writes
  `(x : A) → B x` for the dependent function type, but may use syntax that is closer
  to the standard Π notation and made available in Agda as follows.-}

Π : {A : Type α } (B : A → Type β ) → Type (α ⊔ β)
Π {A = A} B = (x : A) → B x

Π-syntax : (A : Type α)(B : A → Type β) → Type (α ⊔ β)
Π-syntax A B = Π B

syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
infix 6 Π-syntax


module _ {A : Type α }{B : A → Type β} where

 ∣_∣ : Σ[ x ∈ A ] B x → A
 ∣ x , y ∣ = x

 ∥_∥ : (z : Σ[ a ∈ A ] B a) → B ∣ z ∣
 ∥ x , y ∥ = y

 infix  40 ∣_∣ ∥_∥

_⁻¹ : {A : Type α} {x y : A} → x ≡ y → y ≡ x
p ⁻¹ = sym p
infix  40 _⁻¹

_∙_ : {A : Type α}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = trans p q

infixl 30 _∙_

𝑖𝑑 : (A : Type α ) → A → A
𝑖𝑑 A = λ x → x

lift∼lower : {A : Type α} → lift ∘ lower ≡ 𝑖𝑑 (Lift β A)
lift∼lower = refl

lower∼lift : {A : Type α} → lower {α}{β}(lift {α}{β}(λ x → x)) ≡ 𝑖𝑑 A
lower∼lift = refl

_≈_ : {A : Type α } {B : A → Type β } → Π B → Π B → Type (α ⊔ β)
f ≈ g = ∀ x → f x ≡ g x

infix 8 _≈_



transport : {A : Type α } (B : A → Type β) {x y : A} → x ≡ y → B x → B y
transport B refl = id


≡-by-parts : {A : Type α}{B : Type β}{u v : A × B}
 →           fst u ≡ fst v → snd u ≡ snd v → u ≡ v
≡-by-parts refl refl = refl




-- The empty type
data 𝟘 : Type ℓ₀ where  -- maybe we should use ⊥ instead ...?

-- The one element type
data 𝟙 : Type ℓ₀ where
 𝟎 : 𝟙

-- the two element type
data 𝟚 : Type ℓ₀ where  -- Should we use Bool instead?
 𝟎 : 𝟚                  -- Should we use false instead?
 𝟏 : 𝟚                  -- Should we use true instead?

-- the three element type
data 𝟛 : Type ℓ₀ where
 𝟎 : 𝟛
 𝟏 : 𝟛
 𝟐 : 𝟛



\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------

