---
layout: default
title : structures.graph module
date : 2021-05-26
author: William DeMeo
---

This module implements the graph of a structure.  (See Definition 2 of https://arxiv.org/pdf/2010.04958v2.pdf )

Definition [Graph of a structure]. Let ๐จ be an (๐,๐น)-structure (relations from ๐ and operations from ๐น).
The *graph* of ๐จ is the structure Gr ๐จ with the same domain as ๐จ with relations from ๐ and together with a (k+1)-ary relation symbol G ๐ for each ๐ โ ๐น of arity k, which is interpreted in Gr ๐จ as all tuples (t , y) โ Aแตโบยน such that ๐ t โก y.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import agda-imports
open import overture.preliminaries
open import relations.continuous
open import structures.base
open import homs.base

module structures.graph {๐ ๐น : signature}  where

private variable ฮฑ ฯโ : Level

Gr-sig : signature โ signature โ signature
Gr-sig ๐ ๐น = record { symbol = symbol ๐ โ symbol ๐น ; arity = arty }
 where
 arty : symbol ๐ โ symbol ๐น โ Arity
 arty (inl ๐) = (arity ๐) ๐
 arty (inr ๐) = (arity ๐น) ๐ โ ๐


Gr : structure {ฮฑ} ๐ ๐น โ structure (Gr-sig ๐ ๐น) Sigโ
Gr ๐จ = record { carrier = carrier ๐จ ; rel = split ; op = ฮป () }
 where
  split : (๐ : symbol ๐ โ symbol ๐น) โ Rel (carrier ๐จ)
  split (inl ๐) arg = rel ๐จ ๐ arg -- (rel ๐จ) ๐ arg
  split (inr ๐) args = op ๐จ ๐ (args โ inl) โก args (inr ๐)



homโGrhom : {๐จ ๐ฉ : structure {โโ} ๐ {โโ} ๐น} โ hom ๐จ ๐ฉ โ hom (Gr ๐จ) (Gr ๐ฉ)
homโGrhom {๐จ}{๐ฉ} (h , hhom) = h , (i , ii)
 where
  i : is-hom-rel (Gr ๐จ) (Gr ๐ฉ) h
  i (inl ๐) a x = โฃ hhom โฃ ๐ a x
  i (inr ๐) a x = ฮณ
   where
   homop : h (op ๐จ ๐ (a โ inl)) โก op ๐ฉ ๐ (h โ (a โ inl))
   homop = (snd hhom) ๐ (a โ inl)

   ฮณ : op ๐ฉ ๐ (h โ (a โ inl)) โก h (a (inr ๐))
   ฮณ = op ๐ฉ ๐ (h โ (a โ inl)) โกโจ โก-sym homop โฉ
       h (op ๐จ ๐ (a โ inl))   โกโจ cong h x โฉ
       h (a (inr ๐))           โ
  ii : is-hom-op (Gr ๐จ) (Gr ๐ฉ) h
  ii = ฮป ()


Grhomโhom : {๐จ ๐ฉ : structure {โโ} ๐ {โโ} ๐น} โ hom (Gr ๐จ) (Gr ๐ฉ) โ hom ๐จ ๐ฉ
Grhomโhom {๐จ}{๐ฉ} (h , hhom) = h , (i , ii)
 where
  i : is-hom-rel ๐จ ๐ฉ h
  i R a x = fst hhom (inl R) a x
  ii : is-hom-op ๐จ ๐ฉ h
  ii f a = ฮณ
   where
   split : arity ๐น f โ ๐ โ carrier ๐จ
   split (inl x) = a x
   split (inr y) = op ๐จ f a
   ฮณ : h (op ๐จ f a) โก op ๐ฉ f (ฮป x โ h (a x))
   ฮณ = โก-sym (fst hhom (inr f) split refl )



 -- comm-rel : (symbol ๐) โ ((univ ๐จ) โ (univ ๐ฉ)) โ Type ฮฑ
 -- comm-rel ๐ h = โ a โ ((srel ๐จ) ๐ a) โ ((srel ๐ฉ) ๐) (h โ a)

 -- is-hom-rel : ((univ ๐จ) โ (univ ๐ฉ)) โ Type ฮฑ
 -- is-hom-rel h = โ R โ  comm-rel R h

 -- comm-op : (symbol ๐น) โ ((univ ๐จ) โ (univ ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 -- comm-op f h = โ a โ h (((sop ๐จ) f) a) โก ((sop ๐ฉ) f) (h โ a)


 -- is-hom-op : ((univ ๐จ) โ (univ ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 -- is-hom-op h = โ f โ comm-op f h

 -- is-hom : ((univ ๐จ) โ (univ ๐ฉ)) โ Type (ฮฑ โ ฮฒ)
 -- is-hom h = is-hom-rel h ร is-hom-op h

 -- hom : Type (ฮฑ โ ฮฒ)
 -- hom = ฮฃ[ h โ ((univ ๐จ) โ (univ ๐ฉ)) ] is-hom h
 
