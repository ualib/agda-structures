---
layout: default
title : Homs.base
date : 2021-05-22
author: William DeMeo
---

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} -- cubical #-}

open import structures.base


module Homs.base {๐ ๐น : Signature} where

open import agda-imports
open import overture.preliminaries
open import overture.inverses
open import relations.discrete
open import relations.quotients
open import relations.extensionality

open import structures.Congruences {๐ = ๐}{๐น = ๐น}

private variable  ฮฑ ฮฒ : Level
-- ฯ ฯ' ฮณ


-- Development for Structures (Sigma type representation)

module _ (๐จ : Structure ฮฑ ๐ โโ ๐น)(๐ฉ : Structure ฮฒ ๐ โโ ๐น) where

 CompRel : (fst ๐) โ ((fst ๐จ) โ (fst ๐ฉ)) โ Type ฮฑ
 CompRel R h = โ a โ ((R สณ ๐จ) a) โ ((R สณ ๐ฉ) (h โ a))

 IsHom-rel : ((fst ๐จ) โ (fst ๐ฉ)) โ Type ฮฑ
 IsHom-rel h = โ R โ  CompRel R h

 CompOp : (fst ๐น) โ ((fst ๐จ) โ (fst ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 CompOp f h = โ a โ h ((f แต ๐จ) a) โก (f แต ๐ฉ) (h โ a)

 IsHom-op : ((fst ๐จ) โ (fst ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 IsHom-op h = โ f โ CompOp f h

 IsHom : ((fst ๐จ) โ (fst ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 IsHom h = IsHom-rel h ร IsHom-op h

 Hom : Type (ฮฑ โ ฮฒ)
 Hom = ฮฃ[ h โ ((fst ๐จ) โ (fst ๐ฉ)) ] IsHom h

module _ {ฮณ : Level} (๐จ : Structure ฮฑ ๐ โโ ๐น){๐ฉ : Structure ฮฒ ๐ โโ ๐น}(๐ช : Structure ฮณ ๐ โโ ๐น) where

 โ-IsHom-rel : {f : (fst ๐จ) โ (fst ๐ฉ)}{g : (fst ๐ฉ) โ (fst ๐ช)}
  โ             IsHom-rel ๐จ ๐ฉ f โ IsHom-rel ๐ฉ ๐ช g โ IsHom-rel ๐จ ๐ช (g โ f)
 โ-IsHom-rel {f}{g} fhr ghr R a = ฮป z โ ghr R (ฮป zโ โ f (a zโ)) (fhr R a z)

 โ-IsHom-op : {f : (fst ๐จ) โ (fst ๐ฉ)}{g : (fst ๐ฉ) โ (fst ๐ช)}
  โ            IsHom-op ๐จ ๐ฉ f โ IsHom-op ๐ฉ ๐ช g โ IsHom-op ๐จ ๐ช (g โ f)
 โ-IsHom-op {f}{g} fho gho ๐ a = cong g (fho ๐ a) โ gho ๐ (f โ a)

 โ-IsHom : {f : (fst ๐จ) โ (fst ๐ฉ)}{g : (fst ๐ฉ) โ (fst ๐ช)}
  โ         IsHom ๐จ ๐ฉ f โ IsHom ๐ฉ ๐ช g โ IsHom ๐จ ๐ช (g โ f)
 โ-IsHom {f} {g} fhro ghro = ihr , iho
  where
  ihr : IsHom-rel ๐จ ๐ช (g โ f)
  ihr = โ-IsHom-rel {f}{g} (fst fhro) (fst ghro)

  iho : IsHom-op ๐จ ๐ช (g โ f)
  iho = โ-IsHom-op {f}{g} (snd fhro) (snd ghro)

 โ-hom : Hom ๐จ ๐ฉ  โ  Hom ๐ฉ ๐ช  โ  Hom ๐จ ๐ช
 โ-hom (f , fh) (g , gh) = g โ f , โ-IsHom {f}{g} fh gh


๐พ๐น : (๐จ : Structure ฮฑ ๐ โโ ๐น) โ Hom ๐จ ๐จ
๐พ๐น _ = id , (ฮป R a z โ z)  , (ฮป f a โ refl)  -- (ฮป R a โ refl)

module _ (๐จ : Structure ฮฑ ๐ โโ ๐น)(๐ฉ : Structure ฮฒ ๐ โโ ๐น) where

 IsMon : ((fst ๐จ) โ (fst ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 IsMon g = IsHom ๐จ ๐ฉ g ร IsInjective g

 Mon : Type (ฮฑ โ ฮฒ)
 Mon = ฮฃ[ g โ ((fst ๐จ) โ (fst ๐ฉ)) ] IsMon g

 IsEpi : ((fst ๐จ) โ (fst ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 IsEpi g = IsHom ๐จ ๐ฉ g ร IsSurjective g

 Epi : Type (ฮฑ โ ฮฒ)
 Epi = ฮฃ[ g โ ((fst ๐จ) โ (fst ๐ฉ)) ] IsEpi g

MonโHom : (๐จ : Structure ฮฑ ๐ โโ ๐น){๐ฉ : Structure ฮฒ ๐ โโ ๐น} โ Mon ๐จ ๐ฉ โ Hom ๐จ ๐ฉ
MonโHom _ ฯ = (fst ฯ) , fst (snd ฯ )

EpiโHom : {๐จ : Structure ฮฑ ๐ โโ ๐น}(๐ฉ : Structure ฮฒ ๐ โโ ๐น ) โ Epi ๐จ ๐ฉ โ Hom ๐จ ๐ฉ
EpiโHom _ ฯ = (fst ฯ) , fst (snd ฯ)

\end{code}


-- open Lift

-- ๐๐พ๐ป๐ : {ฮฑ ฮฒ : Level}{๐จ : Structure ฮฑ ๐ ๐น} โ hom ๐จ (Lift-str ๐จ ฮฒ)
-- ๐๐พ๐ป๐ = lift , ๐พ๐น

-- ๐โด๐โฏ๐ : {ฮฑ ฮฒ : Level}{๐จ : Structure ฮฑ ๐ ๐น} โ hom (Lift-str ๐จ ฮฒ) ๐จ
-- ๐โด๐โฏ๐ = lower , ๐พ๐น

#### <a id="kernels-of-homomorphisms">Kernels of homomorphisms</a>

The kernel of a homomorphism is a congruence relation and conversely for every congruence relation ฮธ, there exists a homomorphism with kernel ฮธ (namely, that canonical projection onto the quotient modulo ฮธ).

\begin{code}


-- Our first use of the function extensionality THEOREM of Cubical Agda!

module _ {๐จ : Structure ฮฑ ๐ โโ ๐น}{๐ฉ : Structure โโ ๐ โโ ๐น} {wd : swelldef โโ} where
 Homker-comp : (h : Hom ๐จ ๐ฉ) โ Compatible ๐จ (ker (fst h))
 Homker-comp h f {u}{v} kuv = ((fst h) ((f แต ๐จ) u))  โกโจ(snd (snd h)) f u โฉ
                              ((f แต ๐ฉ)((fst h) โ u)) โกโจ wd (f แต ๐ฉ) ((fst h) โ u) ((fst h) โ v) kuv โฉ
                              ((f แต ๐ฉ)((fst h) โ v)) โกโจ((snd (snd h)) f v)โปยน โฉ
                              ((fst h)((f แต ๐จ) v))   โ

 KerCon : Hom ๐จ ๐ฉ โ Con ๐จ
 KerCon h = ฮธ , Cฮธ
  where
  ฮธ : Equivalence โฃ ๐จ โฃ
  ฮธ = ker โฃ h โฃ , ker-IsEquivalence โฃ h โฃ
  Cฮธ : Compatible ๐จ โฃ ฮธ โฃ
  Cฮธ = Homker-comp h

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.

\begin{code}

module _ {๐จ : Structure ฮฑ ๐ โโ ๐น} {wd : swelldef โโ} where
 KerQuo : {๐ฉ : Structure โโ ๐ โโ ๐น} โ Hom ๐จ ๐ฉ โ Structure (lsuc โโ โ ฮฑ) ๐ โโ ๐น
 KerQuo {๐ฉ = ๐ฉ} h = ๐จ โฑ KerCon{๐จ = ๐จ}{๐ฉ = ๐ฉ}{wd = wd} h
 -- _โฑ_ : (๐ฉ : Structure{ฯ} ๐ ๐น {ฮฒ}) โ Con{ฯ} ๐ฉ โ Structure{ฯ} ๐ ๐น {lsuc ฯ โ ฮฒ}

-- module _ {ฮฑ ฮฒ ฯ ฯ : Level} {๐จ : Structure {ฯ} ๐ ๐น {ฮฑ}} where

 -- kerquo : {๐ฉ : Structure {ฯ} ๐ ๐น {ฮฒ}} โ hom ๐จ ๐ฉ โ Structure {ฯ} ๐ ๐น {lsuc ฯ โ ฮฑ} --  {๐ค โ lsuc ๐ฆ}
 -- kerquo {๐ฉ = ๐ฉ} h = ๐จ โฑ {!kercon h!} -- (kercon {๐ฉ = ๐ฉ} h)


-- ker[_โ_]_ : (๐จ : Structure{ฯ} ๐ ๐น {ฮฑ})(๐ฉ : Structure{ฯ} ๐ ๐น {ฮฒ}) โ hom ๐จ ๐ฉ โ Structure ๐ ๐น
-- ker[ ๐จ โ ๐ฉ ] h = kerquo {๐ฉ = ๐ฉ} h

\end{code}

Thus, given `h : hom ๐จ ๐ฉ`, we can construct the quotient of `๐จ` modulo the kernel of `h`, and the syntax for this quotient in the [UniversalAlgebra][] library is `๐จ [ ๐ฉ ]/ker h โพ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `๐จ` and a congruence `ฮธ`, the *canonical projection* is a map from `๐จ` onto `๐จ โฑ ฮธ` that is constructed, and proved epimorphic, as follows.


module _ {๐ฉ : Structure ๐ ๐น {ฮฒ}} where
 open Image_โ_
 ฯepi : (ฮธ : Con{ฮฑ} ๐ฉ) โ epi ๐ฉ (๐ฉ โฑ ฮธ)
 ฯepi ฮธ = (ฮป a โ โช a / โฃ ฮธ โฃ โซ) , (ฮณrel , (ฮป _ _ โ refl)) , cฯ-is-epic  where  -- (ฮป _ _ โ refl)
  ฮณrel : IsHom-rel ๐ฉ (๐ฉ โฑ ฮธ) (ฮป a โ โช a / โฃ ฮธ โฃ โซ)
  ฮณrel R a x = {!!}
  cฯ-is-epic : IsSurjective (ฮป a โ โช a / โฃ ฮธ โฃ โซ)
  cฯ-is-epic (C , (a , Ca)) =  eq (C , (a , Ca)) a ฮป i โ {!!} , {!!} -- Image_โ_.im a

\end{code}

In may happen that we don't care about the surjectivity of `ฯepi`, in which case would might prefer to work with the *homomorphic reduct* of `ฯepi`. This is obtained by applying `epi-to-hom`, like so.


 ฯhom : (ฮธ : Con{๐ค}{๐ฆ} ๐จ) โ hom ๐จ (๐จ โฑ ฮธ)
 ฯhom ฮธ = epi-to-hom (๐จ โฑ ฮธ) (ฯepi ฮธ)

\end{code}


We combine the foregoing to define a function that takes ๐-algebras `๐จ` and `๐ฉ`, and a homomorphism `h : hom ๐จ ๐ฉ` and returns the canonical epimorphism from `๐จ` onto `๐จ [ ๐ฉ ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `๐จ` modulo the kernel of `h`.)


 ฯker : (wd : swelldef ๐ฅ ๐ฆ){๐ฉ : Algebra ๐ฆ ๐}(h : hom ๐จ ๐ฉ) โ epi ๐จ (ker[ ๐จ โ ๐ฉ ] h โพ wd)
 ฯker wd {๐ฉ} h = ฯepi (kercon wd {๐ฉ} h)

\end{code}

The kernel of the canonical projection of `๐จ` onto `๐จ / ฮธ` is equal to `ฮธ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `๐จ / ฮธ โ ฮธ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.


 open IsCongruence

 ker-in-con : {wd : swelldef ๐ฅ (๐ค โ lsuc ๐ฆ)}(ฮธ : Con ๐จ)
  โ           โ {x}{y} โ โฃ kercon wd {๐จ โฑ ฮธ} (ฯhom ฮธ) โฃ x y โ  โฃ ฮธ โฃ x y

 ker-in-con ฮธ hyp = /-โก ฮธ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `๐จ`, a type `I : Type ๐`, and a family `โฌ : I โ Algebra ๐ฆ ๐` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `โฌ` an *indexed family of algebras*.

If in addition we have a family `๐ฝ : (i : I) โ hom ๐จ (โฌ i)` of homomorphisms, then we can construct a homomorphism from `๐จ` to the product `โจ โฌ` in the natural way.


module _ {๐ ๐ฆ : Level}{I : Type ๐}(โฌ : I โ Algebra ๐ฆ ๐) where

 โจ-hom-co : funext ๐ ๐ฆ โ {๐ค : Level}(๐จ : Algebra ๐ค ๐) โ (โ(i : I) โ hom ๐จ (โฌ i)) โ hom ๐จ (โจ โฌ)
 โจ-hom-co fe ๐จ ๐ฝ = ((ฮป a i โ โฃ ๐ฝ i โฃ a)) , (ฮป ๐ ๐ถ โ fe ฮป i โ โฅ ๐ฝ i โฅ ๐ ๐ถ)

\end{code}

The family `๐ฝ` of homomorphisms inhabits the dependent type `ฮ? i ๊ I , hom ๐จ (โฌ i)`.  The syntax we use to represent this type is available to us because of the way `-ฮ?` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`ฮ? ฮป i โ hom ๐จ (โฌ i)` &nbsp; or &nbsp; `(i : I) โ hom ๐จ (โฌ i)` &nbsp; or &nbsp; `โ i โ hom ๐จ (โฌ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `๐ : I โ Algebra ๐ค ๐ and โฌ : I โ Algebra ๐ฆ ๐` (two families of `๐`-algebras), and `๐ฝ :  ฮ? i ๊ I , hom (๐ i)(โฌ i)` (a family of homomorphisms), then we can construct a homomorphism from `โจ ๐` to `โจ โฌ` in the following natural way.


 โจ-hom : funext ๐ ๐ฆ โ {๐ค : Level}(๐ : I โ Algebra ๐ค ๐) โ ฮ?[ i ๊ I ] hom (๐ i)(โฌ i) โ hom (โจ ๐)(โจ โฌ)
 โจ-hom fe ๐ ๐ฝ = (ฮป x i โ โฃ ๐ฝ i โฃ (x i)) , (ฮป ๐ ๐ถ โ fe ฮป i โ โฅ ๐ฝ i โฅ ๐ (ฮป x โ ๐ถ x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.


 โจ-projection-hom : ฮ?[ i ๊ I ] hom (โจ โฌ) (โฌ i)
 โจ-projection-hom = ฮป x โ (ฮป z โ z x) , ฮป _ _ โ refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.





\end{code}















---------- The rest is not yet integrated ------------------------------------------------









(Notice, it is here that the `swelldef` postulate comes into play, and because it is needed to prove `homker-comp`, it is postulated by all the lemmas below that depend upon `homker-comp`.)

It is convenient to define a function that takes a homomorphism and constructs a congruence from its kernel.  We call this function `kercon`.


 kercon : swelldef ๐ฅ ๐ฆ โ {๐ฉ : Algebra ๐ฆ ๐} โ hom ๐จ ๐ฉ โ Con{๐ค}{๐ฆ} ๐จ
 kercon wd {๐ฉ} h = ker โฃ h โฃ , mkcon (ker-IsEquivalence โฃ h โฃ)(homker-comp wd {๐ฉ} h)

\end{code}

With this congruence we construct the corresponding quotient, along with some syntactic sugar to denote it.


 kerquo : swelldef ๐ฅ ๐ฆ โ {๐ฉ : Algebra ๐ฆ ๐} โ hom ๐จ ๐ฉ โ Algebra (๐ค โ lsuc ๐ฆ) ๐
 kerquo wd {๐ฉ} h = ๐จ โฑ (kercon wd {๐ฉ} h)


ker[_โ_]_โพ_ : (๐จ : Algebra ๐ค ๐)(๐ฉ : Algebra ๐ฆ ๐) โ hom ๐จ ๐ฉ โ swelldef ๐ฅ ๐ฆ โ Algebra (๐ค โ lsuc ๐ฆ) ๐
ker[ ๐จ โ ๐ฉ ] h โพ wd = kerquo wd {๐ฉ} h

\end{code}

Thus, given `h : hom ๐จ ๐ฉ`, we can construct the quotient of `๐จ` modulo the kernel of `h`, and the syntax for this quotient in the [UniversalAlgebra][] library is `๐จ [ ๐ฉ ]/ker h โพ fe`.



#### <a id="the-canonical-projection">The canonical projection</a>

Given an algebra `๐จ` and a congruence `ฮธ`, the *canonical projection* is a map from `๐จ` onto `๐จ โฑ ฮธ` that is constructed, and proved epimorphic, as follows.


module _ {๐ค ๐ฆ : Level}{๐จ : Algebra ๐ค ๐} where
 ฯepi : (ฮธ : Con{๐ค}{๐ฆ} ๐จ) โ epi ๐จ (๐จ โฑ ฮธ)
 ฯepi ฮธ = (ฮป a โ โช a โซ) , (ฮป _ _ โ refl) , cฯ-is-epic  where
  cฯ-is-epic : IsSurjective (ฮป a โ โช a โซ)
  cฯ-is-epic (C , (a , refl)) =  Image_โ_.im a

\end{code}

In may happen that we don't care about the surjectivity of `ฯepi`, in which case would might prefer to work with the *homomorphic reduct* of `ฯepi`. This is obtained by applying `epi-to-hom`, like so.


 ฯhom : (ฮธ : Con{๐ค}{๐ฆ} ๐จ) โ hom ๐จ (๐จ โฑ ฮธ)
 ฯhom ฮธ = epi-to-hom (๐จ โฑ ฮธ) (ฯepi ฮธ)

\end{code}


We combine the foregoing to define a function that takes ๐-algebras `๐จ` and `๐ฉ`, and a homomorphism `h : hom ๐จ ๐ฉ` and returns the canonical epimorphism from `๐จ` onto `๐จ [ ๐ฉ ]/ker h`. (Recall, the latter is the special notation we defined above for the quotient of `๐จ` modulo the kernel of `h`.)


 ฯker : (wd : swelldef ๐ฅ ๐ฆ){๐ฉ : Algebra ๐ฆ ๐}(h : hom ๐จ ๐ฉ) โ epi ๐จ (ker[ ๐จ โ ๐ฉ ] h โพ wd)
 ฯker wd {๐ฉ} h = ฯepi (kercon wd {๐ฉ} h)

\end{code}

The kernel of the canonical projection of `๐จ` onto `๐จ / ฮธ` is equal to `ฮธ`, but since equality of inhabitants of certain types (like `Congruence` or `Rel`) can be a tricky business, we settle for proving the containment `๐จ / ฮธ โ ฮธ`. Of the two containments, this is the easier one to prove; luckily it is also the one we need later.


 open IsCongruence

 ker-in-con : {wd : swelldef ๐ฅ (๐ค โ lsuc ๐ฆ)}(ฮธ : Con ๐จ)
  โ           โ {x}{y} โ โฃ kercon wd {๐จ โฑ ฮธ} (ฯhom ฮธ) โฃ x y โ  โฃ ฮธ โฃ x y

 ker-in-con ฮธ hyp = /-โก ฮธ hyp

\end{code}



#### <a id="product-homomorphisms">Product homomorphisms</a>

Suppose we have an algebra `๐จ`, a type `I : Type ๐`, and a family `โฌ : I โ Algebra ๐ฆ ๐` of algebras.  We sometimes refer to the inhabitants of `I` as *indices*, and call `โฌ` an *indexed family of algebras*.

If in addition we have a family `๐ฝ : (i : I) โ hom ๐จ (โฌ i)` of homomorphisms, then we can construct a homomorphism from `๐จ` to the product `โจ โฌ` in the natural way.


module _ {๐ ๐ฆ : Level}{I : Type ๐}(โฌ : I โ Algebra ๐ฆ ๐) where

 โจ-hom-co : funext ๐ ๐ฆ โ {๐ค : Level}(๐จ : Algebra ๐ค ๐) โ (โ(i : I) โ hom ๐จ (โฌ i)) โ hom ๐จ (โจ โฌ)
 โจ-hom-co fe ๐จ ๐ฝ = (ฮป a i โ โฃ ๐ฝ i โฃ a) , (ฮป ๐ ๐ถ โ fe ฮป i โ โฅ ๐ฝ i โฅ ๐ ๐ถ)

\end{code}

The family `๐ฝ` of homomorphisms inhabits the dependent type `ฮ? i ๊ I , hom ๐จ (โฌ i)`.  The syntax we use to represent this type is available to us because of the way `-ฮ?` is defined in the [Type Topology][] library.  We like this syntax because it is very close to the notation one finds in the standard type theory literature.  However,
we could equally well have used one of the following alternatives, which may be closer to "standard Agda" syntax:

`ฮ? ฮป i โ hom ๐จ (โฌ i)` &nbsp; or &nbsp; `(i : I) โ hom ๐จ (โฌ i)` &nbsp; or &nbsp; `โ i โ hom ๐จ (โฌ i)`.

The foregoing generalizes easily to the case in which the domain is also a product of a family of algebras. That is, if we are given `๐ : I โ Algebra ๐ค ๐ and โฌ : I โ Algebra ๐ฆ ๐` (two families of `๐`-algebras), and `๐ฝ :  ฮ? i ๊ I , hom (๐ i)(โฌ i)` (a family of homomorphisms), then we can construct a homomorphism from `โจ ๐` to `โจ โฌ` in the following natural way.


 โจ-hom : funext ๐ ๐ฆ โ {๐ค : Level}(๐ : I โ Algebra ๐ค ๐) โ ฮ?[ i ๊ I ] hom (๐ i)(โฌ i) โ hom (โจ ๐)(โจ โฌ)
 โจ-hom fe ๐ ๐ฝ = (ฮป x i โ โฃ ๐ฝ i โฃ (x i)) , (ฮป ๐ ๐ถ โ fe ฮป i โ โฅ ๐ฝ i โฅ ๐ (ฮป x โ ๐ถ x i))

\end{code}



#### <a id="projections-out-of-products">Projection out of products</a>

Later we will need a proof of the fact that projecting out of a product algebra onto one of its factors is a homomorphism.


 โจ-projection-hom : ฮ?[ i ๊ I ] hom (โจ โฌ) (โฌ i)
 โจ-projection-hom = ฮป x โ (ฮป z โ z x) , ฮป _ _ โ refl

\end{code}

We could prove a more general result involving projections onto multiple factors, but so far the single-factor result has sufficed.


{% include UALib.Links.md %}









Detailed proofs.
```
 โ-IsHom-rel : {f : โฃ ๐จ โฃ โ โฃ ๐ฉ โฃ}{g : โฃ ๐ฉ โฃ โ โฃ ๐ช โฃ}
  โ             IsHom-rel ๐จ ๐ฉ f โ IsHom-rel ๐ฉ ๐ช g โ IsHom-rel ๐จ ๐ช (g โ f)
 โ-IsHom-rel {f}{g} fhr ghr R a = pf
  where
  pf : ((R สณ ๐จ) a) โก (R สณ ๐ช)(g โ f โ a)
  pf = (R สณ ๐จ) a          โกโจ fhr R a โฉ
       (R สณ ๐ฉ)(f โ a)     โกโจ ghr R (f โ a)โฉ
       (R สณ ๐ช)(g โ f โ a) โ

 โ-IsHom-op : {f : โฃ ๐จ โฃ โ โฃ ๐ฉ โฃ}{g : โฃ ๐ฉ โฃ โ โฃ ๐ช โฃ}
  โ            IsHom-op ๐จ ๐ฉ f โ IsHom-op ๐ฉ ๐ช g โ IsHom-op ๐จ ๐ช (g โ f)
 โ-IsHom-op {f}{g} fho gho ๐ a = pf
  where
  pf : (g โ f) ((๐ แต ๐จ) a) โก (๐ แต ๐ช) (ฮป x โ (g โ f) (a x))
  pf = (g โ f) ((๐ แต ๐จ) a) โกโจ cong g (fho ๐ a)โฉ
       g ((๐ แต ๐ฉ)(f โ a)) โกโจ gho ๐ (f โ a) โฉ
       (๐ แต ๐ช) (ฮป x โ (g โ f) (a x)) โ


```
  hghr : โ R a โ ((R สณ ๐จ) a) โก (R สณ ๐ช)(h โ g โ a)
  hghr R a = (R สณ ๐จ) a          โกโจ ghr R a โฉ
             (R สณ ๐ฉ)(g โ a)     โกโจ hhr R (g โ a)โฉ
             (R สณ ๐ช)(h โ g โ a) โ

  hgho : โ ๐ a โ (h โ g)((๐ แต ๐จ) a) โก (๐ แต ๐ช)(h โ g โ a)
  hgho ๐ a = (h โ g)((๐ แต ๐จ) a) โกโจ cong h (gho ๐ a)โฉ
             h ((๐ แต ๐ฉ)(g โ a)) โกโจ hho ๐ (g โ a)โฉ
             (๐ แต ๐ช)(h โ g โ a) โ
open import Agda.Primitive using (_โ_; lsuc)


open import Cubical.Core.Primitives using (_โก_; Type; Level; _,_; ฮฃ-syntax;  i0; i1; fst; snd)
open import Cubical.Foundations.Prelude using (refl; sym; _โ_; funExt; cong; _โ; _โกโจ_โฉ_)
open import Cubical.Foundations.Function using (_โ_)
open import Cubical.Data.Sigma.Base using (_ร_)
open import Cubical.HITs.TypeQuotients -- .Base where


-- Imports from the Agda Universal Algebra Library
open import structures.basic using (Signature; Structure; _สณ_; _แต_; compatible)
open import overture.preliminaries using (id; _โปยน; โฃ_โฃ; โฅ_โฅ)
open import overture.inverses using (IsInjective; IsSurjective; Image_โ_; im)
open import relations.discrete using (ker; ker')
open import relations.quotients using (ker-IsEquivalence; โช_/_โซ)

