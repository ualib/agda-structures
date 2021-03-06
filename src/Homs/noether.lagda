---
layout: default
title : Homomorphisms.Noether module (The Agda Universal Algebra Library)
date : 2021-05-22
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}


open import structures.base


module homs.noether {π πΉ : Signature} where
open import agda-imports
open import overture.preliminaries
open import overture.inverses
open import relations.discrete
open import relations.quotients
open import relations.truncation
open import relations.extensionality

open import structures.congruences {π = π}{πΉ = πΉ} using (Con; _β±_)
open import homs.base {π = π}{πΉ = πΉ}

\end{code}


#### <a id="the-first-homomorphism-theorem">The First Homomorphism Theorem</a>

\begin{code}

private variable  Ο Ο' Ξ³ : Level

FirstHomTheorem|Set :

    (π¨ : Structure{Ο} π πΉ {Ξ±})(π© : Structure{Ο} π πΉ {Ξ±})(h : hom π¨ π©)
    (pe : pred-ext ? ?)(fe : swelldef ? ?)                              -- extensionality assumptions
    (Bset : is-set β£ π© β£)(buip : blk-uip β£ π¨ β£ β£ kercon fe {π©} h β£)     -- truncation assumptions
    -----------------------------------------------------------------------------------------------------------
 β  Ξ£[ Ο κ hom (ker[ π¨ β π© ] h βΎ fe) π©  ] ((β£ h β£ β‘ β£ Ο β£ β β£ Οker fe{π©}h β£) Γ IsInjective β£ Ο β£ Γ is-embedding β£ Ο β£)

FirstHomTheorem|Set π¨ π© h pe fe Bset buip = (Ο , Οhom) , refl , Οmon , Οemb
 where
  ΞΈ : Con π¨
  ΞΈ = kercon fe{π©} h
  ΞΎ : IsEquivalence β£ ΞΈ β£
  ΞΎ = IsCongruence.is-equivalence β₯ ΞΈ β₯

  Ο : β£ (ker[ π¨ β π© ] h βΎ fe) β£ β β£ π© β£
  Ο a = β£ h β£ β a β

  Οhom : is-homomorphism (ker[ π¨ β π© ] h βΎ fe) π© Ο
  Οhom π a = β£ h β£ ( (π Μ π¨) (Ξ» x β β a x β) ) β‘β¨ β₯ h β₯ π (Ξ» x β β a x β)  β©
             (π Μ π©) (β£ h β£ β (Ξ» x β β a x β))  β‘β¨ cong (π Μ π©) refl β©
             (π Μ π©) (Ξ» x β Ο (a x))            β

  Οmon : IsInjective Ο
  Οmon {_ , (u , refl)} {_ , (v , refl)} Οuv = block-ext|uip pe buip ΞΎ Οuv

  Οemb : is-embedding Ο
  Οemb = monic-is-embedding|Set Ο Bset Οmon

\end{code}

Below we will prove that the homomorphism `Ο`, whose existence we just proved, is unique (see `NoetherHomUnique`), but first we show that if we add to the hypotheses of the first homomorphism theorem the assumption that `h` is surjective, then we obtain the so-called *first isomorphism theorem*.  Naturally, we let `FirstHomTheorem|Set` do most of the work. (Note that the proof also requires an additional local function extensionality postulate.)

\begin{code}

FirstIsoTheorem|Set :

     (π¨ : Algebra π€ π)(π© : Algebra π¦ π)(h : hom π¨ π©)
     (pe : pred-ext π€ π¦)(fe : swelldef π₯ π¦)(fww : funext π¦ π¦)       -- extensionality assumptions
     (Bset : is-set β£ π© β£)(buip : blk-uip β£ π¨ β£ β£ kercon fe{π©}h β£)  -- truncation assumptions
 β   IsSurjective β£ h β£
     -----------------------------------------------------------------------------------------------------------
 β   Ξ£[ f β (epi (ker[ π¨ β π© ] h βΎ fe) π©)] (β£ h β£ β‘ β£ f β£ β β£ Οker fe{π©}h β£) Γ IsInjective β£ f β£ Γ is-embedding β£ f β£

FirstIsoTheorem|Set π¨ π© h pe fe fww Bset buip hE = (fmap , fhom , fepic) , refl , (snd β₯ FHT β₯)
 where
  FHT = FirstHomTheorem|Set π¨ π© h pe fe Bset buip

  fmap : β£ ker[ π¨ β π© ] h βΎ fe β£ β β£ π© β£
  fmap = fst β£ FHT β£

  fhom : is-homomorphism (ker[ π¨ β π© ] h βΎ fe) π© fmap
  fhom = snd β£ FHT β£

  fepic : IsSurjective fmap
  fepic b = Ξ³ where
   a : β£ π¨ β£
   a = SurjInv β£ h β£ hE b

   bfa : b β‘ fmap βͺ a β«
   bfa = (cong-app (SurjInvIsRightInv {fe = fww} β£ h β£ hE) b)β»ΒΉ

   Ξ³ : Image fmap β b
   Ξ³ = Image_β_.eq b βͺ a β« bfa

\end{code}

Now we prove that the homomorphism `Ο`, whose existence is guaranteed by `FirstHomTheorem|Set`, is unique.

\begin{code}

module _ {fe : swelldef π₯ π¦}(π¨ : Algebra π€ π)(π© : Algebra π¦ π)(h : hom π¨ π©) where

 NoetherHomUnique : (f g : hom (ker[ π¨ β π© ] h βΎ fe) π©)
  β                 β£ h β£ β‘ β£ f β£ β β£ Οker fe{π©}h β£ β β£ h β£ β‘ β£ g β£ β β£ Οker fe{π©}h β£
  β                 β a  β  β£ f β£ a β‘ β£ g β£ a

 NoetherHomUnique f g hfk hgk (_ , (a , refl)) = β£ f β£ (_ , (a , refl)) β‘β¨ cong-app(hfk β»ΒΉ)a β©
                                                 β£ h β£ a                β‘β¨ cong-app(hgk)a β©
                                                 β£ g β£ (_ , (a , refl)) β

\end{code}

If, in addition, we postulate extensionality of functions defined on the domain `ker[ π¨ β π© ] h`, then we obtain the following variation of the last result.<sup>[1](Homomorphisms.Noether.html#fn1)</sup>

\begin{code}

 fe-NoetherHomUnique : {fuww : funext (π€ β lsuc π¦) π¦}(f g : hom (ker[ π¨ β π© ] h βΎ fe) π©)
  β  β£ h β£ β‘ β£ f β£ β β£ Οker fe{π©}h β£  β  β£ h β£ β‘ β£ g β£ β β£ Οker fe{π©}h β£  β  β£ f β£ β‘ β£ g β£

 fe-NoetherHomUnique {fuww} f g hfk hgk = fuww (NoetherHomUnique f g hfk hgk)

\end{code}

The proof of `NoetherHomUnique` goes through for the special case of epimorphisms, as we now verify.

\begin{code}

 NoetherIsoUnique : (f g : epi (ker[ π¨ β π© ] h βΎ fe) π©)
  β                 β£ h β£ β‘ β£ f β£ β β£ Οker fe{π©}h β£ β β£ h β£ β‘ β£ g β£ β β£ Οker fe{π©}h β£
  β                 β a β β£ f β£ a β‘ β£ g β£ a

 NoetherIsoUnique f g hfk hgk = NoetherHomUnique (epi-to-hom π© f) (epi-to-hom π© g) hfk hgk

\end{code}







#### <a id="homomorphism-decomposition">Homomorphism decomposition</a>

If `Ξ± : hom π¨ π©`, `Ξ² : hom π¨ πͺ`, `Ξ²` is surjective, and `ker Ξ² β ker Ξ±`, then there exists `Ο : hom πͺ π©` such that `Ξ± = Ο β Ξ²` so the following diagram commutes:

```
π¨ --- Ξ² ->> πͺ
 \         .
  \       .
   Ξ±     Ο
    \   .
     \ .
      V
      π©
```

\begin{code}

module _ {π¨ : Algebra π§ π}{πͺ : Algebra π© π} where

 HomFactor : funext π§ π¨ β funext π© π© β (π© : Algebra π¨ π)(Ξ± : hom π¨ π©)(Ξ² : hom π¨ πͺ)
  β          kernel β£ Ξ² β£ β kernel β£ Ξ± β£ β IsSurjective β£ Ξ² β£
             -------------------------------------------
  β          Ξ£[ Ο β (hom πͺ π©)] β£ Ξ± β£ β‘ β£ Ο β£ β β£ Ξ² β£

 HomFactor fxy fzz π© Ξ± Ξ² KΞ²Ξ± Ξ²E = (Ο , ΟIsHomCB) , Ξ±ΟΞ²
  where
   Ξ²Inv : β£ πͺ β£ β β£ π¨ β£
   Ξ²Inv = SurjInv β£ Ξ² β£ Ξ²E

   Ξ· : β£ Ξ² β£ β Ξ²Inv β‘ ππ β£ πͺ β£
   Ξ· = SurjInvIsRightInv{fe = fzz} β£ Ξ² β£ Ξ²E

   Ο : β£ πͺ β£ β β£ π© β£
   Ο = β£ Ξ± β£ β Ξ²Inv

   ΞΎ : β a β kernel β£ Ξ² β£ (a , Ξ²Inv (β£ Ξ² β£ a))
   ΞΎ a = (cong-app Ξ· (β£ Ξ² β£ a))β»ΒΉ

   Ξ±ΟΞ² : β£ Ξ± β£ β‘ Ο β β£ Ξ² β£
   Ξ±ΟΞ² = fxy Ξ» x β KΞ²Ξ± (ΞΎ x)

   ΟIsHomCB : β π c β Ο ((π Μ πͺ) c) β‘ ((π Μ π©)(Ο β c))
   ΟIsHomCB π c = Ο ((π Μ πͺ) c)                    β‘β¨ cong(Ο β(π Μ πͺ))(cong (Ξ» - β - β c)Ξ· β»ΒΉ)β©
                  Ο ((π Μ πͺ)(β£ Ξ² β£ β(Ξ²Inv β c)))   β‘β¨ cong Ο (β₯ Ξ² β₯ π (Ξ²Inv β c))β»ΒΉ β©
                  Ο (β£ Ξ² β£((π Μ π¨)(Ξ²Inv β c)))     β‘β¨ cong-app(Ξ±ΟΞ² β»ΒΉ)((π Μ π¨)(Ξ²Inv β c))β©
                  β£ Ξ± β£((π Μ π¨)(Ξ²Inv β c))         β‘β¨ β₯ Ξ± β₯ π (Ξ²Inv β c) β©
                  (π Μ π©)(Ξ» x β β£ Ξ± β£(Ξ²Inv (c x))) β

\end{code}

If, in addition to the hypotheses of the last theorem, we assume Ξ± is epic, then so is Ο. (Note that the proof also requires an additional local function extensionality postulate, `funext π¨ π¨`.)

\begin{code}

 HomFactorEpi : funext π§ π¨ β funext π© π© β funext π¨ π¨
  β             (π© : Algebra π¨ π)(Ξ± : hom π¨ π©)(Ξ² : hom π¨ πͺ)
  β             kernel β£ Ξ² β£ β kernel β£ Ξ± β£ β IsSurjective β£ Ξ² β£ β IsSurjective β£ Ξ± β£
                ----------------------------------------------------------
  β             Ξ£[ Ο β epi πͺ π© ] β£ Ξ± β£ β‘ β£ Ο β£ β β£ Ξ² β£

 HomFactorEpi fxy fzz fyy π© Ξ± Ξ² kerincl Ξ²e Ξ±e = (fst β£ ΟF β£ ,(snd β£ ΟF β£ , ΟE)), β₯ ΟF β₯
  where
   ΟF : Ξ£[ Ο β hom πͺ π© ] β£ Ξ± β£ β‘ β£ Ο β£ β β£ Ξ² β£
   ΟF = HomFactor fxy fzz π© Ξ± Ξ² kerincl Ξ²e

   Ο : β£ πͺ β£ β β£ π© β£
   Ο = β£ Ξ± β£ β (SurjInv β£ Ξ² β£ Ξ²e)

   ΟE : IsSurjective Ο
   ΟE = epic-factor {fe = fyy} β£ Ξ± β£ β£ Ξ² β£ Ο β₯ ΟF β₯ Ξ±e

\end{code}


--------------------------------------

<sup>1</sup><span class="footnote" id="fn1"> See [Relations.Truncation][] for a discussion of *truncation*, *sets*, and *uniqueness of identity proofs*.</span>

<sup>2</sup><span class="footnote" id="fn2"> In this module we are already assuming *global* function extensionality (`gfe`), and we could just appeal to `gfe` (e.g., in the proof of `FirstHomomorphismTheorem`) instead of adding local function extensionality (\ab{fe}) to the list of assumptions.  However, we sometimes add an extra extensionality postulate in order to highlight where and how the principle is applied.}</span>

<br>
<br>

[β Homomorphisms.Basic](Homomorphisms.Basic.html)
<span style="float:right;">[Homomorphisms.Isomorphisms β](Homomorphisms.Isomorphisms.html)</span>

{% include UALib.Links.md %}
















-- Imports from the Agda (Builtin) and the Agda Standard Library
open import Agda.Builtin.Equality using (_β‘_; refl)
open import Axiom.Extensionality.Propositional renaming (Extensionality to funext)
open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Product using (_,_; Ξ£; _Γ_; Ξ£-syntax)
open import Function.Base  using (_β_; id)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; cong-app)
open import Relation.Unary using (_β_)

-- Imports from the Agda Universal Algebra Library
open import Algebras.Basic
open import Overture.Preliminaries using (Type; π; π€; π₯; π¦; π§; π¨; π©; Ξ ; -Ξ ; -Ξ£; _β‘β¨_β©_; _β; _β»ΒΉ; β£_β£; β₯_β₯; fst; snd; ππ)
open import Overture.Inverses using (IsInjective; IsSurjective; Image_β_; SurjInv)
open import Relations.Discrete using (ker; kernel)
open import Relations.Quotients using (ker-IsEquivalence; _/_; βͺ_β«; β_β)
open import Relations.Truncation using (is-set; blk-uip; is-embedding; monic-is-embedding|Set)
open import Relations.Extensionality using (swelldef;  block-ext|uip; pred-ext; SurjInvIsRightInv; epic-factor)

