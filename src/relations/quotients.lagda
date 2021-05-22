---
layout: default
title : Relations.Quotients module (The Agda Universal Algebra Library)
date : 2021-01-13
author: William DeMeo
---

### <a id="equivalence-relations-and-quotients">Equivalence Relations and Quotients</a>

This section presents the [Relations.Quotients][] module of the [Agda Universal Algebra Library][].

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

module relations.quotients where

open import agda-imports
open import overture.preliminaries
open import Relation.Binary renaming (Rel to BinRel) using (IsEquivalence)
open import relations.continuous public

Equivalence : {α β : Level} → Type β → Type (lsuc α ⊔ β)
Equivalence {α}{β} B = Σ[ r ∈ BinRel B α ] IsEquivalence r

ker-IsEquivalence : {A : Type α}{B : Type β}(f : A → B) → IsEquivalence (ker f)
ker-IsEquivalence f = record { refl = refl ; sym = λ x → sym x ; trans = λ x y → trans x y }


{- Blocks of partitions.
   Before defining the quotient type, we define a type representing inhabitants of quotients;
   i.e., blocks of a partition (recall partitions correspond to equivalence relations) -}

module _ {α β : Level}  where

 [_/_] : {B : Type β} → B → Equivalence{α} B → Pred B α
 [ u / R ] = ∣ R ∣ u


 record IsBlock {B : Type β}(C : Pred B α){R : Equivalence{α} B} : Type (lsuc α ⊔ β) where
  constructor R-block
  field
   block-u : B
   C≡[u] : C ≡ [ block-u / R ]

 _/_ : (B : Type β ) → Equivalence{α} B → Type (lsuc α ⊔ β)
 _/_ B R = Σ[ C ∈ Pred B α ] IsBlock C {R}

 infix -1 _/_

 ⟪_/_⟫ : {B : Type β} → B → (R : Equivalence{α} B) → B / R
 ⟪ a / R ⟫ = [ a / R ] , R-block a refl

 ⌞_⌟ : {B : Type β}{R : Equivalence{α} B} → B / R  → B
 ⌞ _ , R-block a _ ⌟ = a



≡→⊆ : {B : Type β}(P Q : Pred B α) → P ≡ Q → P ⊆ Q
≡→⊆ P .P refl {x} Px = Px

module _ {B : Type β}{R : Equivalence{α} B} where

 -- ([]-⊆ used to be called /-subset)
 []-⊆ :  ∀ x y → ∣ R ∣ x y → [ x / R ] ⊆  [ y / R ]
 []-⊆ x y Rxy {z} Rxz = IsEquivalence.trans (snd R) (IsEquivalence.sym (snd R) Rxy) Rxz

 -- ([]-⊇ used to be called /-supset)
 []-⊇ : ∀ x y → ∣ R ∣ x y → [ y / R ] ⊆ [ x / R ]
 []-⊇ x y Rxy {z} Ryz = IsEquivalence.trans (snd R) Rxy Ryz

 ⊆-[] : ∀ x y → [ x / R ] ⊆ [ y / R ] → ∣ R ∣ x y
 ⊆-[] x y xy = IsEquivalence.sym (snd R) (xy (IsEquivalence.refl (snd R)))

 ⊇-[] : ∀ x y → [ y / R ] ⊆ [ x / R ] → ∣ R ∣ x y
 ⊇-[] x y yx = yx (IsEquivalence.refl (snd R))

 related : ∀ x y → [ x / R ] ≡ [ y / R ] → ∣ R ∣ x y
 related x y xy = IsEquivalence.sym (snd R) (≡→⊆ [ x / R ] [ y / R ] xy (IsEquivalence.refl (snd R)))

 []≡-elim : {u v : B} → [ u / R ] ≡ [ v / R ] → ∣ R ∣ u v
 []≡-elim {u}{v} uv = goal
  where
  ξ : v ∈ [ v / R ]
  ξ = (IsEquivalence.refl (snd R))
  goal : v ∈ [ u / R ]
  goal = ≡→⊆ [ v / R ] [ u / R ] (uv ⁻¹) ξ -- transp (λ i → (uv ⁻¹) i v ) i0 ξ


 -- Can we prove the converse... ?
 -- isProp : {B : Type β}(P : Pred B α) → Type (β ⊔ α)
 -- isProp P = ∀ x → (p q : x ∈ P) → p ≡ q
 -- []≡-intro : (u v : B) → isProp [ u / R ] → isProp [ v / R ] → ∣ R ∣ u v → [ u / R ] ≡ [ v / R ]
 -- []≡-intro u v propu propv uv = {!!}
 -- PropExt ([ u / R ]ₙ) ([ v / R ]ₙ) propu propv ([]-⊆ uv) ([]-⊇ uv)



\end{code}

An example application of these is the `block-ext` type in the [Relations.Extensionality] module.



-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------






















<!-- NO LONGER NEEDED ------------------------------------------------------------






-- infix 60 [_/_]ₙ

module _ {B : Type β}{R : Equivalence{α} B} where

   
 []-⊆ : {u v : B} → ∣ R ∣ u v →  [ u / R ]ₙ ⊆ [ v / R ]ₙ
 []-⊆ {u}{v} Ruv {x} ux = transitive ∥ R ∥ v u x (symmetric ∥ R ∥ u v Ruv) ux

 []-⊇ : {u v : B} → ∣ R ∣ u v → [ v / R ]ₙ ⊆ [ u / R ]ₙ
 []-⊇ {u}{v} Ruv {x} Rvx = transitive ∥ R ∥ u v x Ruv Rvx

 {- If we assume that for each x there is at most one proof that x ∈ [ u / R ],
    and similarly for x ∈ [ v / R ], then we can prove the following equivalence
    of blocks of an equivalence relation. -}


 IsBlock : (C : Pred B _) → Type (lsuc α ⊔ β)
 IsBlock C = Σ[ u ∈ B ] C ≡ [ u / R ]ₙ


-- Quotients.
_/_ : (B : Type β ) → Equivalence{α} B → Type (lsuc α ⊔ β)
B / R = Σ[ C ∈ Pred B _ ] IsBlock {R = R} C

infix -1 _/_
module _ {B : Type β} where

 ⟪_/_⟫ : B → (R : Equivalence {α} B) → B / R
 ⟪ b / R ⟫ = [ b / R ]ₙ , (b  , refl)

 _⌞_⌟ : (R : Equivalence {α} B) → B / R  → B
 R ⌞ C , b , p ⌟ = b

module _ {B : Type β}{R : Equivalence {α} B} where

 ⟪⟫≡-elim : {u v : B} → ⟪ u / R ⟫ ≡ ⟪ v / R ⟫ → ∣ R ∣ u v
 ⟪⟫≡-elim uv = []≡-elim {R = R}(cong fst uv)

\end{code}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (_⊔_; lzero; lsuc; Level; Setω)
open import Data.Product  using (_,_; Σ; Σ-syntax; _×_)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Unary using (Pred; _⊆_)

-- -- Imports from the Agda (Builtin) and the Agda Standard Library
-- open import Agda.Primitive using (_⊔_; lsuc)
-- open import Relation.Unary using (Pred; _∈_; _⊆_)
-- open import Function.Base using (_on_)

-- -- Imports from Cubical Agda
-- open import Cubical.Core.Primitives --  using (_≡_; Type; Level; _,_; Σ-syntax; Typeω; transp; i0; i1; fst)
-- open import Cubical.Foundations.Prelude using (refl; sym; _∙_; cong; isProp)
-- open import Cubical.Foundations.Function using (_∘_)
-- open import Cubical.Relation.Binary.Base as CBinary renaming (Rel to REL) using (EquivRel)
-- open CBinary.BinaryRelation renaming (isEquivRel to IsEquivalence)
-- -- open import Cubical.HITs.TypeQuotients using (_/ₜ_; [_]; eq/)

-- open import Cubical.Data.Sigma using (_×_)

-- open import overture.preliminaries using (∣_∣; ∥_∥; _⁻¹)
-- open import relations.discrete renaming (Rel to BinRel) using (ker; PropExt)









---------------------------------------------------------------------------- -->

{- Old quotient development.

   The next two submodules contain the types we previously used for handling quotients.
   These may still be of some use even after we incorporate the "type quotient" defined
   as a higher inductive type in Cubical Agda as follows:

   ```
   -- Type quotients as a higher inductive type:
   data _/ₜ_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
   [_] : (a : A) → A /ₜ R
   eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
   ```
-}
-- Type quotients as a higher inductive type (lifted from the
-- Cubical.HITs.SetQuotients.Base module of Cubical Agda .
data _/ₕ_ {α β} (B : Type β) (R : BinRel B α) : Type (α ⊔ β) where
 [_] : (x : B) → B /ₕ R
 eq/ : (x y : B) → (r : R x y) → [ x ] ≡ [ y ]
-- squash/ : ([x] [y] : B /ₕ R) → (p q : [x] ≡ [y]) → p ≡ q

module _ {B : Type β}{R : BinRel B α} {P : Pred (B /ₕ R) γ} where

 
 elim[] : ((x y : B) (r : R x y) → PathP (λ i → P (eq/ x y r i)) x y)
  →       (x : B /ₕ R) → P x
 elim[] peq x = ?
--  elim[] (squash/ x x₁ p q i i₁) = {!!}
 

\end{code}

[_/_]ₙ : {B : Type β} → B → Equivalence{α} B → Pred B α
[ u / R ]ₙ = ∣ R ∣ u
variable
 α β : Level

-- Refl : {A : Type α} → BinRel A β → Type(α ⊔ β)
-- Refl _≈_ = ∀{x} → x ≈ x

-- Symm : {A : Type α} → BinRel A β → Type(α ⊔ β)
-- Symm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x

-- Antisymm : {A : Type α} → BinRel A β → Type(α ⊔ β)
-- Antisymm _≈_ = ∀{x}{y} → x ≈ y → y ≈ x → x ≡ y

-- Trans : {A : Type α} → BinRel A β → Type(α ⊔ β)
-- Trans _≈_ = ∀{x}{y}{z} → x ≈ y → y ≈ z → x ≈ z

-- Equivalence : {α β : Level} → Type β → Type (lsuc α ⊔ β)
-- Equivalence {α}{β} B = Σ[ r ∈ BinRel B α ] IsEquivalence r

-- open IsEquivalence

-- module _ {I : Type 𝓥} {A : Type α } where

--  𝟎 : BinRel (I → A) (𝓥 ⊔ α)
--  𝟎 x y = ∀ i → x i ≡ y i

--  𝟎-IsEquivalence : IsEquivalence 𝟎
--  𝟎-IsEquivalence = equivRel
--                    (λ a i _ → a i)                        -- reflexive
--                    (λ a b p i i₁ → sym (p i) i₁)          -- symmetric
--                    (λ a b c p q i i₁ → ((p i)∙(q i)) i₁)  -- transitive

--  𝟎-IsEquivalence' : IsEquivalence 𝟎
--  𝟎-IsEquivalence' = record
--                     { reflexive = λ a i → refl
--                     ; symmetric = λ a b x i → sym (x i)
--                     ; transitive = λ a b c x y i → (x i ∙ y i) }


-- 𝟎-is-smallest : Typeω
-- 𝟎-is-smallest = ∀{𝓥}{α}{β}{I : Type 𝓥}{A : Type α}(ρ : BinRel (I → A) β)
--  →              IsEquivalence ρ → (x y : I → A) → 𝟎 x y → ρ x y


-- kernel-lemma : {𝓥 α : Level} → 𝟎-is-smallest
--  →             {I : Type 𝓥}{A : Type α}(f : (I → A) → A)(x y : I → A)
--  →             (∀ i → x i ≡ y i) → (ker f) x y

-- kernel-lemma {𝓥}{α} 0min {I = I}{A = A} f x y hyp =
--  0min (ker f) (ker-IsEquivalence{α = (𝓥 ⊔ α)}{A = (I → A)} f) x y hyp


Thus, `v ∈ [ u ]` if and only if `R u v`, as desired.  We often refer to `[ u ]` as the `R`-*block containing* `u`.

A predicate `C` over `A` is an `R`-block if and only if `C ≡ [ u ]` for some `u : A`.  We represent this characterization of an `R`-block as follows.


If `R` is an equivalence relation on `A`, then the *quotient* of `A` modulo `R` is denoted by `A / R` and is defined to be the collection `{[ u ] ∣  y : A}` of all `R`-blocks.<sup>[1](Relations.Quotients.html#fn1)</sup>

We use the following type to represent an \ab R-block with a designated representative.

