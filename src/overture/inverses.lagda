---
layout: default
title : overture.inverses module (cubical-algebras library)
date : 2021-05-10
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} --  --cubical #-}

module overture.inverses where

open import agda-imports
open import overture.preliminaries

private variable α β : Level

module _ {A : Type α }{B : Type β } where

 -- inverse images of functions
 data Image_∋_ (f : A → B) : B → Type (α ⊔ β)
  where
  eq : {b : B} → (a : A) → b ≡ f a → Image f ∋ b

 ImageIsImage : (f : A → B)(b : B)(a : A) → b ≡ f a → Image f ∋ b
 ImageIsImage f b a b≡fa = eq a b≡fa

 ImageTransfer : (f : A → B)(b1 b2 : B) → Image f ∋ b1 → b1 ≡ b2 → Image f ∋ b2
 ImageTransfer f b1 b2 (eq {.b1} a x) b1b2 = eq a (b1b2 ⁻¹ ∙ x)


module _ {A : Type α }{B : A → Type β } where

 data DepImage_∋_ (f : (a : A) → B a) : Σ[ a ∈ A ] B a → Type (α ⊔ β) where
  dim : (x : A) → DepImage f ∋ (x , f x)
  deq : ((a , b) : Σ[ a ∈ A ] B a) → b ≡ f a → DepImage f ∋ (a , b)


 DepImageIsImage : (f : (a : A) → B a)(a : A)(b : B a) → b ≡ f a → DepImage f ∋ (a , b)
 DepImageIsImage f a b b≡fa = deq (a , b) b≡fa


 DepImageTransfer : (f : (a : A) → B a)(a : A)(b1 b2 : B a)
  →                 DepImage f ∋ (a , b1) → b1 ≡ b2 → DepImage f ∋ (a , b2)

 DepImageTransfer f a .(f a) b2 (dim .a) p2 = deq (a , b2) (p2 ⁻¹)
 DepImageTransfer f a b1 b2 (deq .(a , b1) x) p2 = deq (a , b2) (p2 ⁻¹ ∙ x)


\end{code}

An inhabitant of `Image f ∋ b` is a dependent pair `(a , p)`, where `a : A` and `p : b ≡ f a` is a proof that `f` maps `a` to `b`.  Since the proof that `b` belongs to the image of `f` is always accompanied by a witness `a : A`, we can actually *compute* a (pseudo)inverse of `f`. For convenience, we define this inverse function, which we call `Inv`, and which takes an arbitrary `b : B` and a (*witness*, *proof*)-pair, `(a , p) : Image f ∋ b`, and returns the witness `a`.

\begin{code}

module _ {A : Type α }{B : Type β } where

 Inv : (f : A → B){b : B} → Image f ∋ b  →  A
 Inv f (eq a _) = a

 Inv' : (f : A → B)(b : B){imfb : Image f ∋ b}  →  A
 Inv' f b {eq a x} = a

 inv : (f : A → B)(b : B) → Image f ∋ b →  A
 inv f b (eq a x) = a

\end{code}

We can prove that `Inv f` is the *right-inverse* of `f`, as follows.

\begin{code}

 InvIsInv : (f : A → B){b : B}(q : Image f ∋ b) → f(Inv f q) ≡ b
 InvIsInv f (eq _ p) = p ⁻¹

 InvIsInv' : (f : A → B)(b : B){q : Image f ∋ b} → f(Inv' f b {q}) ≡ b
 InvIsInv' f b {eq _ p} = p ⁻¹

 inv-is-inv : (f : A → B)(b : B)(q : Image f ∋ b) → f(inv f b q) ≡ b
 inv-is-inv f b (eq a x) = x ⁻¹

 InvIsLeftInv : {f : A → B}{x : A} → (Inv f){f x} (eq x refl)  ≡ x
 InvIsLeftInv = refl



\end{code}

The inverse image of each point in the codomain of a function can be represented as follows.

\begin{code}

 InvImage : (f : A → B) → B → Pred A β
 InvImage f b a = f a ≡ b

\end{code}

Thus, for each point `b : B`, `InvImage f b` returns a (possibly empty) predicate on `A` which represents all points `a : A` such that `f a ≡ b`.

#### <a id="injective-functions">Injective functions</a>

We say that a function `f : A → B` is *injective* (or *monic*) if it does not map two distinct elements of the domain to the same point in the codomain. The following types manifest this property.

\begin{code}

module _ {A : Type α}{B : Type β} where

 IsInjective : (A → B) → Type (α ⊔ β)
 IsInjective f = ∀ {x y} → f x ≡ f y → x ≡ y

 Injective : Type (α ⊔ β)
 Injective = Σ[ f ∈ (A → B) ] IsInjective f

 Range : (f : A → B) → Pred B (α ⊔ β)
 Range f b = ∃[ a ] f a ≡ b

 -- data range (f : A → B) : Type (α ⊔ β)
 --  where
 --  rim : (x : A) → range f
 --  req : (b : B) → ∃[ a ∈ A ] f a ≡ b → range f

 -- Image→Range : (f : A → B)(b : B) → Image f ∋ b → b ∈ Range f
 -- Image→Range f .(f x) (im x) = x , refl
 -- Image→Range f b (eq .b a x) = a , (x ⁻¹)

 -- Range→Image : (f : A → B)(b : B) → b ∈ Range f → Image f ∋ b
 -- Range→Image f b ranfb = eq b (fst ranfb) (snd ranfb ⁻¹)

 data Option {α : Level}(A : Type α) : Type α where
  some : A → Option A
  none : Option A

\end{code}

If we have an injective function `f : A → B` and for all `b : B` the assertion `b ∈ Range f` is *decidable* (that is, we can decide whether or not any given `b` is in the range of `f`), then we can define a partial inverse function that returns `some a` if `a` is the preimage of `b` and returns `none` if `b` is not in the range of `f`.

\begin{code}

 InjInv : (f : A → B) → (∀ b → Dec (b ∈ Range f)) → IsInjective f → B → Option A
 InjInv f dec finj b = invaux b (dec b)
  where
  Ranfb : B → Type (α ⊔ β)
  Ranfb b = b ∈ Range f

  invaux : (b : B) → Dec (Ranfb b) → Option A
  invaux b (false because _) = none
  invaux b (true because ofʸ (a , _)) = some a

\end{code}

Before moving on to discuss surjective functions, let us prove (the obvious facts) that the identity map is injective and that the composition of injectives is injective.

\begin{code}

id-is-injective : {A : Type α} → IsInjective{A = A}{B = A} (λ x → x)
id-is-injective = λ z → z

private variable γ : Level

∘-injective : {A : Type α}{B : Type β}{C : Type γ}{f : A → B}{g : B → C}
 →            IsInjective f → IsInjective g → IsInjective (g ∘ f)
∘-injective finj ginj = λ z → finj (ginj z)

\end{code}


#### <a id="epics">Surjective functions</a>

A *surjective function* from `A` to `B` is a function `f : A → B` such that for all `b : B` there exists `a : A` such that `f a ≡ b`.  In other words, the range and codomain of `f` agree.  The following types manifest this notion.

\begin{code}

module _ {α β : Level}{A : Type α}{B : Type β} where
 IsSurjective : (A → B) →  Type (α ⊔ β)
 IsSurjective f = ∀ y → Image f ∋ y

 Surjective : Type (α ⊔ β)
 Surjective = Σ[ f ∈ (A → B) ] IsSurjective f

\end{code}

With the next definition, we can represent a *right-inverse* of a surjective function.

\begin{code}

 SurjInv : (f : A → B) → IsSurjective f → B → A
 SurjInv f fE b = Inv f (fE b)

\end{code}

Thus, a right-inverse of `f` is obtained by applying `SurjInv` to `f` and a proof of `IsSurjective f`.  Later, we will prove that this does indeed give the right-inverse, but we postpone the proof since it requires function extensionality, a concept we take up in the [Relations.Extensionality][] module.

For now, we settle for proof of the fact that `SurjInv` is a point-wise right-inverse.

\begin{code}

 SurjInvIsRightInv≈ : (f : A → B)(fE : IsSurjective f) → f ∘ (SurjInv f fE) ≈ 𝑖𝑑 B
 SurjInvIsRightInv≈ f fE = λ x → InvIsInv f (fE x)

module _ {α β : Level}{A : Type α}{B : Type β} where

 IsBijective : (A → B) →  Type (α ⊔ β)
 IsBijective f = IsInjective f × IsSurjective f

 Bijective : Type (α ⊔ β)
 Bijective = Σ[ f ∈ (A → B) ] IsBijective f

\end{code}

With the next definition we represent the inverse of a bijective function.

\begin{code}

 BijInv : (f : A → B) → IsBijective f → B → A
 BijInv f fb b = Inv f {b} ((snd fb) b)

\end{code}

Thus, an inverse of `f` is obtained by applying `Inv` to `f` and a proof of `IsSurjective f`.

[TODO: prove that `BijInv f` is both a left and right inverse of `f`. (see notes at bottom of this file) ]


\begin{code}

module _ {α β : Level}{A : Type α}{B : Type β} where

 InvIsRInv≈ : (f : A → B)(fb : IsBijective f) → f ∘ (BijInv f fb) ≈ 𝑖𝑑 B
 InvIsRInv≈ f fb = λ x → InvIsInv f ((snd fb) x)

\end{code}

-------------------------------------------------------------------
--                        THE END                                --
-------------------------------------------------------------------


























 -- InvIsLInv≈ : (f : A → B)(fb : IsBijective f) → (BijInv f fb) ∘ f ≈ 𝑖𝑑 A
 -- InvIsLInv≈ f (finj , fsurj) x = γ
 --  where
 --  ζ : (InjInv' f finj) (f x)(im x) ≡ x
 --  ζ = refl

 --  invf : (b : B) → Image f ∋ b → A
 --  invf .(f x) (im x) = x
 --  invf b (eq .b a x) = a

 --  η : Image f ∋ (f x)
 --  η = im x

 --  ξ : Inv f η ≡ x
 --  ξ = refl

 --  eqinj : (a : A) → f x ≡ f a → a ≡ x
 --  eqinj a fxfa = finj (fxfa ⁻¹)

 --  ρ : f (Inv f {f x} (fsurj (f x))) ≡ f x
 --  ρ = f (Inv f {f x} (fsurj (f x))) ≡⟨ {!!} ⟩ -- cong (f ∘ (Inv f {f x})) refl
 --      f (Inv f {f x} (im x)) ≡⟨ refl  ⟩
 --      f x ∎

 --  γ : (BijInv f (finj , fsurj) ∘ f) x ≡ 𝑖𝑑 A x
 --  γ = (BijInv f (finj , fsurj) ∘ f) x ≡⟨ finj ρ ⟩
 --      Inv f {f x} (im x) ≡⟨ refl ⟩
 --      𝑖𝑑 A x ∎
