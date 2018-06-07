Baire Category Theorem.
-----------------------

This article gives a formal statement of the Baire category theorem.  For wikipedia's
description, see `Baire category theorem <https://en.wikipedia.org/wiki/Baire_category_theorem>`_

The following statements comprise the Baire category theorem.

informal **Baire category theorem (BCT1-a)** 

   Every [complete] [metric space] is a [Baire] [topological space].

preformal :: 
  
  theorem Baire_category_theorem_BCT1_a :=
  ∀ (X : complete, metric space), Baire X. 

informal **Baire category theorem (BCT1-b)**  
  
   Every [topological space] which is [homeomorphic] to an [open] subset of a
   [complete] [pseudometric space] is a [Baire] [topological space].

preformal    ::
  
   theorem Baire_category_theorem_BCT1_b :=
   ∀ (X : topological space), (∃ (S : pseudometric space), ∃ U,
   open S U ∧ homeomorphic X U) → Baire X.

informal **Baire category theorem BCT2**   
  
   Every [locally compact] [Hausdorff] [topological space] is a [Baire] [topological space]. 

preformal    ::
  
   ∀ (X : locally compact, Hausdorff, topological space), Baire X.

informal **Baire category theorem BCT3** 
  
   A [non-empty] [complete] [metric space] is not the [countable union] of [nowhere-dense] [closed sets].

preformal      ::
  
   ∀ (X : nonempty, complete, metric space), ¬∃ F,
   countable F ∧ every nowhere-dense F ∧ every closed F ∧ X = ⋃ F.


notes
=====

* A topological space is Baire if every countable intersection of open dense sets is dense.
