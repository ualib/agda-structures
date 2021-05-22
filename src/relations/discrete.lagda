---
layout: default
title : relations.discrete module
date : 2021-05-20
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}



module relations.discrete where

open import agda-imports
open import overture.preliminaries
open import Relation.Binary.Core renaming (REL to BinREL; Rel to BinRel) public

variable
 𝓥 : Level

{-Unary relations. The unary relation (or "predicate") type is imported from
  Relation.Unary of the std lib.
  ```
  Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
  Pred A ℓ = A → Set ℓ
  ```
-}

module _ {α β : Level}{B : Type β}
         (P Q : Pred B α) where

 -- Naturally, if P ≡ Q, then P ⊆ Q and Q ⊆ P.
 -- ≡→⊆ : P ≡ Q → P ⊆ Q
 -- ≡→⊆ pq {x} Px = subst (λ p → x ∈ p) pq Px -- transp (λ i → pq i x) i0 Px

 -- In cubical tt, we can also prove the converse!
 -- PropExt : (∀ x → isProp (P x)) → (∀ x → isProp (Q x)) → P ⊆ Q → Q ⊆ P → P ≡ Q
 -- PropExt Pprop Qprop φ ψ = funExt goal
 --  where
 --  goal : (x : B) → P x ≡ Q x
 --  goal x = hPropExt (Pprop x) (Qprop x) φ ψ


{-Binary relations. The binary relation types are called `Rel` and `REL` in the standard library, but we
  will call them BinRel and BinREL and reserve the names Rel and REL for the more general types of
  relations we define in the relations.continuous module.

  The heterogeneous binary relation type is imported from the standard library and renamed BinREL.
  ```
  BinREL : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  BinREL A B ℓ' = A → B → Type ℓ'
  ```
  The homogeneous binary relation type is imported from the standard library and renamed BinRel.
  ```
  BinRel : ∀{ℓ} → Type ℓ → (ℓ' : Level) → Type (ℓ ⊔ lsuc ℓ')
  BinRel A ℓ' = REL A A ℓ'
  ```
-}

module _ {A : Type α}{B : Type β} where

 ker : (A → B) → BinRel A β
 ker g x y = g x ≡ g y

 ker' : (A → B) → (I : Type 𝓥) → BinRel (I → A) (β ⊔ 𝓥)
 ker' g I x y = g ∘ x ≡ g ∘ y

 kernel : (A → B) → Pred (A × A) β
 kernel g (x , y) = g x ≡ g y


module _ {B : Type β} where


 𝟎 : BinRel B β
 𝟎 = _≡_

 𝟎-pred : Pred (B × B) β
 𝟎-pred (x , y) = x ≡ y

 𝟎-sigma : Type β
 𝟎-sigma = Σ[ x ∈ B ] Σ[ y ∈ B ] x ≡ y



private variable γ : Level

-- The following type denotes the assertion that the image of a given
-- function is contained in a given subset of the codomain.
Im_⊆_ : {A : Type α}{B : Type β} → (A → B) → Pred B γ → Type (α ⊔ γ)
Im f ⊆ S = ∀ x → f x ∈ S



-- Operation symbols.
-- We now define the type of operation symbols of arity `I : Type lzero` over the type `A : Type α`.
Arity : Type ℓ₁
Arity = Type ℓ₀  -- Assuming for now that all arity types have universe level 0.
                 -- This is merely for notational convenience, and it's not clear
                 -- whether it's a real restriction---are there use-cases requiring
                 -- arities inhabiting higher types?

-- The type of operation symbols.
Op : Arity → Type α → Type α
Op I A = (I → A) → A

-- Example (projections)
π : {I : Arity} {A : Type α } → I → Op I A
π i x = x i


{-Compatibility of binary relations.
  We now define the function `compatible` so that, if `𝑩` denotes a structure and `r` a binary
  relation, then `compatible 𝑩 r` will represent the assertion that `r` is *compatible* with all
  basic operations of `𝑩`. in the following sense:
  `∀ 𝑓 : ∣ 𝐹 ∣ → ∀(x y : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣) → (∀ i → r (x i)(y i)) → r (f x)(f y)` -}

eval-rel : {A : Type α}{I : Arity} → BinRel A β → BinRel (I → A) β
eval-rel R u v = ∀ i → R (u i) (v i)

compatible-op : {A : Type α}{I : Arity} → Op I A → BinRel A β → Type (α ⊔ β)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

--Fancy notation for compatible-op.
_|:_ : {A : Type α}{I : Arity} → Op I A → BinRel A β → Type _
f |: R  = (eval-rel R) =[ f ]⇒ R

\end{code}


-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------




data _[_]_ {β : Level} {B : Type β} (x : B) (α : Level) : B → Type (α ⊔ β) where
 instance REFL : x [ α ] x

infix 4 _[_]_

module _ {α β : Level} {B : Type β} where

 𝟎' : BinRel B (α ⊔ β)
 𝟎' x y = x [ α ] y

 𝟎-pred' : Pred (B × B) (α ⊔ β)
 𝟎-pred' (x , y) = x [ α ] y

 𝟎-sigma' : Type (α ⊔ β)
 𝟎-sigma' = Σ[ x ∈ B ] Σ[ y ∈ B ] x [ α ] y
