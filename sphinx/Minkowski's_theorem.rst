Minkowski's Theorem
-------------------

This article gives a formal statement of Minkowski's theorem.  For Wikipedia's
description, see `Mikowski's theorem <https://en.wikipedia.org/wiki/Minkowski%27s_theorem>`_

Informal statement
   Suppose that L is a lattice of determinant d(L)
   in the n-dimensional real vector space ℝn and
   S is a convex subset of ℝn that is symmetric with respect to the origin,
   meaning that if x is in S then −x is also in S.
   If the volume of S is strictly greater than 2n d(L),
   then S must contain at least one lattice point other than the origin. 

.. code-block:: text

  notation:
  (L : lattice, subset ℝⁿ)
  (S : convex, centrally symmetric, subset ℝⁿ)
  (d := lattice_determinant L)
  (vol := Lebesgue_measure S)

  theorem Minkowki's :=
  (vol > 2^n * d → (L ∩ S ≠ {0}))

Note: A convex subset of Rn is Lebesgue `measurable <https://math.stackexchange.com/questions/207609/the-measurability-of-convex-sets>`_.  (This should be added to wiki somewhere, either in Minkowski's theorem or convex sets.)

The appropriate notion of symmetry here is centrally symmetric with respect to the origin.

