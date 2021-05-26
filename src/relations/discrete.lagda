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

-- Operation symbols.
-- We now define the type of operation symbols of arity `I : Type lzero` over the type `A : Type α`.
Arity : Type ℓ₁
Arity = Type ℓ₀  -- Assuming for now that all arity types have universe level 0.
                 -- This is merely for notational convenience, and it's not clear
                 -- whether it's a real restriction---are there use-cases requiring
                 -- arities inhabiting higher types?


{-Unary relations. The unary relation (or "predicate") type is imported from
  Relation.Unary of the std lib.
  ```
  Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
  Pred A ℓ = A → Set ℓ
  ```
-}

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
module _ {α β : Level}
         {A : Type α}{B : Type β}
         where


 ker : (A → B) → BinRel A β
 ker g x y = g x ≡ g y

 ker' : (A → B) → (I : Arity) → BinRel (I → A) β
 ker' g I x y = g ∘ x ≡ g ∘ y

 kernel : (A → B) → Pred (A × A) β
 kernel g (x , y) = g x ≡ g y


module _ {α ρ : Level}{A : Type (α ⊔ ρ)} where

-- Subset containment relation for binary realtions
 _⊑_ : BinRel A ρ → BinRel A ρ → Type (α ⊔ ρ)
 P ⊑ Q = ∀ x y → P x y → Q x y

 ⊑-refl : {P : BinRel A ρ} → P ⊑ P
 ⊑-refl x y Pxy = Pxy

 ⊑-trans : {P Q R : BinRel A ρ} → P ⊑ Q → Q ⊑ R → P ⊑ R
 ⊑-trans {P = P}{Q}{R} PQ QR x y Pxy = QR x y (PQ x y Pxy)




 -- 𝟎 : BinRel A (α ⊔ β)
 -- 𝟎 x y = Lift α (x ≡ y)
 -- 𝟎 : BinRel A ρ
 -- 𝟎 x y = {!!} -- x ≡ y

 -- 𝟎-pred : Pred (A × A) α
 -- 𝟎-pred (x , y) = {!!} -- x ≡ y

 -- 𝟎-sigma : Type α
 -- 𝟎-sigma = {!!} -- Σ[ x ∈ A ] Σ[ y ∈ A ] x ≡ y



private variable α β ρ : Level

-- The following type denotes the assertion that the image of a given
-- function is contained in a given subset of the codomain.
Im_⊆_ : {A : Type α}{B : Type β} → (A → B) → Pred B ρ → Type (α ⊔ ρ)
Im f ⊆ S = ∀ x → f x ∈ S



-- The type of operation symbols.
Op : Arity → Type α → Type α
Op I A = (I → A) → A

-- New notation for operations on A of arity I

𝒪 : Type α → {I : Arity} → Type α
𝒪 A {I} = (I → A) → A

-- Example (projections)
π : {I : Arity} {A : Type α } → I → Op I A
π i x = x i

π' : {I : Arity} {A : Type α } → I → 𝒪 A
π' i x = x i


{-Compatibility of binary relations.
  We now define the function `compatible` so that, if `𝑩` denotes a structure and `r` a binary
  relation, then `compatible 𝑩 r` will represent the assertion that `r` is *compatible* with all
  basic operations of `𝑩`. in the following sense:
  `∀ 𝑓 : ∣ 𝐹 ∣ → ∀(x y : ∥ 𝐹 ∥ 𝑓 → ∣ 𝑩 ∣) → (∀ i → r (x i)(y i)) → r (f x)(f y)` -}

eval-rel : {A : Type α}{I : Arity} → BinRel A β → BinRel (I → A) β
eval-rel R u v = ∀ i → R (u i) (v i)

compatible-op : {A : Type α}{I : Arity} → 𝒪 A{I} → BinRel A β → Type (α ⊔ β)
compatible-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

comp-op : {A : Type α}{I : Arity} → 𝒪 A{I}  → BinRel A β → Type (α ⊔ β)
comp-op f R  = ∀ u v → (eval-rel R) u v → R (f u) (f v)

--Fancy notation for compatible-op.
_|:_ : {A : Type α}{I : Arity} → 𝒪 A{I} → BinRel A β → Type (α ⊔ β)
f |: R  = (eval-rel R) =[ f ]⇒ R

compatagree : {A : Type α}{I : Arity}{f : 𝒪 A{I}}{R : BinRel A β}
 →            compatible-op f R → f |: R
compatagree {f = f}{R} c {x}{y} Rxy = c x y Rxy

compatagree' : {A : Type α}{I : Arity}{f : 𝒪 A{I}}{R : BinRel A β}
 →             f |: R → compatible-op f R
compatagree' {f = f}{R} c = λ u v x → c x

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
