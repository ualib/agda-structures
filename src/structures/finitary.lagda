---
layout: default
title : structures.finitary module
date : 2021-06-01
author: William DeMeo
---

This is the base submodule of the structures module which presents finitary (relational-algebraic) structures as inhabitants of record types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module structures.finitary where

open import agda-imports
open import overture.preliminaries
open import relations.continuous

private
  variable
    α β γ ρ ρ₀ ρ₁ : Level
    A : Type α
    B : Type β
    C : Type γ

-- n-ary operations on A
Op[_] : (A : Type α) (n : ℕ) → Type α
Op[ A ] n = (Fin n → A) → A


-- All operations on A
O[_] : (A : Type α) → Type α
O[ A ] = Σ[ n ∈ ℕ ] Op[ A ] n

-- n-ary relations on A
Rel[_] : (A : Type α) {ρ : Level} (n : ℕ) → Type (α ⊔ lsuc ρ)
Rel[ A ]{ρ} n = (Fin n → A) → Type ρ


-- All operations on A
R[_∣_] : (A : Type α)(ρ : Level) → Type (α ⊔ lsuc ρ)
R[ A ∣ ρ ] = Σ[ n ∈ ℕ ] Rel[ A ]{ρ} n


record finSignature : Type ℓ₁ where
 field
  symbol : Type ℓ₀
  arity : symbol → ℕ

open finSignature public


record finStructure {α ρ ϕ : Level} : Type (lsuc (α ⊔ ρ ⊔ ϕ)) where -- (lsuc (α ⊔ ρ)) where
 field
  carrier : Type α
  rel : Pred R[ carrier ∣ ρ ] ϕ
  ops : Pred O[ carrier ] ϕ

  -- ∀ (𝑟 : symbol 𝑅) → Rel carrier {Fin (arity 𝑅 𝑟)} {ρ}  -- interpretations of relations
open finStructure public

-- eval-rel : {A : Type α}{I : Arity} → BinRel A β → BinRel (I → A) β
-- eval-rel R u v = ∀ i → R (u i) (v i)

compatible-finop : {A : Type α} → O[ A ] → BinRel A β → Type (α ⊔ β)
compatible-finop (n , f) R = ∀ u v → (eval-rel R) u v → R (f u) (f v)

--Fancy notation for compatible-op.
_o|:_ : {A : Type α} → O[ A ] → BinRel A β → Type (α ⊔ β)
(n , f) o|: R  = (eval-rel R) =[ f ]⇒ R

-- compatible : {α ρ ϕ : Level}(𝑨 : finStructure {α}{ρ}{ϕ}) → BinRel (carrier 𝑨) β → Type (α ⊔ β)
-- compatible 𝑨 r = ∀ 𝑓 → 𝑓 ∈ ops 𝑨 → 𝑓 |: r

\end{code}


module _ {α ρ : Level}{𝑅 𝐹 : signature} where

 open Lift

 Lift-op : {I : Arity}{A : Type α} → Op A{I} → (ℓ : Level) → Op (Lift ℓ A){I}
 Lift-op f ℓ = λ x → lift (f (λ i → lower (x i)))

 Lift-rel : {I : Arity}{A : Type α} → Rel A {I}{ρ} → (ℓ : Level) → Rel (Lift ℓ A) {I}{ρ}
 Lift-rel r ℓ x = r (λ i → lower (x i))

 Lift-structure : structure {α} 𝑅 {ρ} 𝐹 → (ℓ : Level) → structure {α ⊔ ℓ} 𝑅 {ρ} 𝐹
 Lift-structure 𝑨 ℓ = record { carrier = Lift ℓ (carrier 𝑨) ; rel = lrel ; op = lop }
  where
  lrel : (r : symbol 𝑅 ) → Rel (Lift ℓ (carrier 𝑨)){arity 𝑅 r}{ρ}
  lrel r = λ x → ((rel 𝑨)r) (λ i → lower (x i))
  lop : (f : symbol 𝐹) → Op (Lift ℓ (carrier 𝑨)) {arity 𝐹 f}
  lop f = λ x → lift (((op 𝑨) f)( λ i → lower (x i)))



-- Some examples (of finite signatures)
-- The signature with...
-- ... no symbols  (e.g., sets)
Sig∅ : signature
Sig∅ = record { symbol = 𝟘 ; arity = λ () }

-- ... one nulary symbol (e.g., pointed sets)
Sig-0 : signature
Sig-0 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟘 }

Sig-1 : signature -- ...one unary
Sig-1 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟙 }

-- ...one binary symbol (e.g., magmas, semigroups, semilattices)
Sig-2 : signature
Sig-2 = record { symbol = 𝟙 ; arity = λ 𝟎 → 𝟚 }

-- ...one nulary and one binary (e.g., monoids)
Sig-0-1 : signature
Sig-0-1 = record { symbol = 𝟚 ; arity = λ{ 𝟎 → 𝟘 ; 𝟏 → 𝟚 } }

-- ...one nulary, one unary, and one binary (e.g., groups)
Sig-0-1-2 : signature
Sig-0-1-2 = record { symbol = 𝟛 ; arity = λ{ 𝟎 → 𝟘 ; 𝟏 → 𝟙 ; 𝟐 → 𝟚 } }
\end{code}








-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------



































-- -- Inhabitants of Signature type are pairs, (s , ar), where s is an operation or
-- -- relation symbol and ar its arity.
-- Signature : Type ℓ₁
-- Signature = Σ[ F ∈ Type ℓ₀ ] (F → Arity)

-- Structure : (α : Level) → Signature → (ρ : Level) → Signature → Type (lsuc (α ⊔ ρ))
-- Structure  α 𝑅 ρ 𝐹 =
--  Σ[ A ∈ Type α ]                        -- the domain of the structure is A
--   ( ((r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r}{ρ})  -- the interpretations of the relation symbols
--   × ((f : ∣ 𝐹 ∣) → Op A{snd 𝐹 f}) )     -- the interpretations of the operation symbols

-- -- Relations of arbitrary arity over a single sort.
-- -- Rel : Type α → {I : Arity} → {ρ : Level} → Type (α ⊔ lsuc ρ)
-- -- Rel A {I} {ρ} = (I → A) → Type ρ

-- RStructure : (α : Level) → Signature → (ρ : Level) → Type (lsuc (α ⊔ ρ))
-- RStructure α 𝑅 ρ = Σ[ A ∈ Type α ] ∀(r : ∣ 𝑅 ∣) → Rel A {snd 𝑅 r} {ρ}
-- -- Rel : Arity → Type α → (β : Level) → Type (α ⊔ lsuc β)
-- -- Rel ar A β = (ar → A) → Type β

-- AStructure : (α : Level) → Signature → Type (lsuc α)
-- AStructure α 𝐹 = Σ[ A ∈ Type α ] ∀ (f : ∣ 𝐹 ∣) → Op A {snd 𝐹 f}

-- -- Reducts
-- Structure→AStructure : {α ρ : Level} {𝑅 𝐹 : Signature} → Structure α 𝑅 ρ 𝐹 → AStructure α 𝐹
-- Structure→AStructure (A , (_ , ℱ)) = A , ℱ

-- Structure→RStructure : {α ρ : Level}{𝑅 𝐹 : Signature} → Structure α 𝑅 ρ 𝐹 → RStructure α 𝑅 ρ
-- Structure→RStructure (A , (ℛ , _)) = A , ℛ
-- module _ {α ρ : Level}{𝑅 𝐹 : Signature}  where
-- {- Let 𝑅 and 𝐹 be signatures and let ℬ = (B , (ℛ , ℱ)) be an (𝑅, 𝐹)-structure.
--    - If `r : ∣ 𝑅 ∣` is a relation symbol, then `rel ℬ r` is the interpretation of `r` in `ℬ`.
--    - if `f : ∣ 𝐹 ∣` is an opereation symbol, then `op ℬ f` is the interpretation
--    of `f` in `ℬ`. -}

--   -- Syntax for interpretation of relations and operations.
--   _⟦_⟧ᵣ : (𝒜 : Structure α 𝑅 ρ 𝐹)(𝑟 : fst 𝑅) → Rel (fst 𝒜) {snd 𝑅 𝑟} {ρ}
--   𝒜 ⟦ 𝑟 ⟧ᵣ = λ a → (∣ snd 𝒜 ∣ 𝑟) a

--   _⟦_⟧ₒ : (𝒜 : Structure α 𝑅 ρ 𝐹)(𝑓 : fst 𝐹) → Op (fst 𝒜) {snd 𝐹 𝑓}
--   𝒜 ⟦ 𝑓 ⟧ₒ = λ a → (snd (snd 𝒜) 𝑓) a

--   _ʳ_ : (𝑟 : fst 𝑅)(𝒜 : Structure α 𝑅 ρ _) → Rel (fst 𝒜){(snd 𝑅) 𝑟}{ρ}
--   𝑟 ʳ 𝒜 = λ a → (𝒜 ⟦ 𝑟 ⟧ᵣ) a

--   _ᵒ_ : (𝑓 : fst 𝐹)(𝒜 : Structure α _ ρ 𝐹) → Op (fst 𝒜){snd 𝐹 𝑓} 
--   𝑓 ᵒ 𝒜 = λ a → (𝒜 ⟦ 𝑓 ⟧ₒ) a

-- module _ {α ρ : Level}{𝑅 𝐹 : Signature}  where
--  Compatible : {ρ' : Level}(𝑨 : Structure α 𝑅 ρ 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
--  Compatible 𝑨 r = ∀ 𝑓 → (𝑓 ᵒ 𝑨) |: r

--  Compatible' : {ρ' : Level}(𝑨 : Structure α 𝑅 ρ 𝐹) → BinRel (fst 𝑨) ρ'  → Type (α ⊔ ρ')
--  Compatible' 𝑨 r = ∀ 𝑓 → compatible-op (𝑓 ᵒ 𝑨) r

