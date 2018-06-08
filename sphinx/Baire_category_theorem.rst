Baire Category Theorem.
-----------------------

This article gives a formal statement of the Baire category theorem.  For wikipedia's
description, see `Baire category theorem <https://en.wikipedia.org/wiki/Baire_category_theorem>`_

The following statements comprise the Baire category theorem.

informal **Baire category theorem (BCT1-a)** 

   Every [complete] [metric space] is a [Baire] [topological space].

preformal ::

  notation:
  (X : complete, metric space)
  
  theorem Baire_category_theorem_BCT1_a :=
  Baire X. 

informal **Baire category theorem (BCT1-b)**  
  
   Every [topological space] which is [homeomorphic] to an [open] subset of a
   [complete] [pseudometric space] is a [Baire] [topological space].

preformal    ::

  notation:
  (X : topological space)
  (S : pseudometric space)
  (U : open, subset S)
  (_ : homeomorphic X U)
  
   theorem Baire_category_theorem_BCT1_b :=
   Baire X.

informal **Baire category theorem BCT2**   
  
   Every [locally compact] [Hausdorff] [topological space] is a [Baire] [topological space]. 

preformal    ::

  notation:
  (X : locally compact, Hausdorff, topological space)

  theorem Baire_category_BCT2 :=
  Baire X.

notes
=====

* A topological space is Baire if every countable intersection of open dense sets is dense.
* The definitions of `Cauchy and completeness <https://www.math.wustl.edu/~freiwald/ch4.pdf>`_
  apply to both metric and pseudometric spaces.  Wikipedia only discusses completeness for metric spaces.
