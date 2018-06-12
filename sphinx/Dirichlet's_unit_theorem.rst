Dirichlet's unit theorem
------------------------

This article gives a formal statement of Dirichlet's unit theorem.  For Wikipedia's
description, see `Dirichlet's unit theorem <https://en.wikipedia.org/wiki/Dirichlet%27s_unit_theorem>`_.

Informal statement

  Let K be an algebraic number field with ring OK of algebraic integers.
  The group of units in the ring OK of is finitely generated and has rank 
  r1 + r2 − 1
  where r1 is the number of real embeddings and r2 the number of
  conjugate pairs of complex embeddings of K.

.. code-block:: text

  notation:
  (K : number field)
  (OK := algebraic_integer K)
  (U := (unit_group OK : abelian, group))
  (n := degree K ℚ)
  (r₁ := card(real_field_embedding K, function K ℝ))

  theorem Dirichlet's_unit_theorem :=
  (finitely_generated U) ∧
  (rank U = (n + r₁)/2 - 1)

Notes
=====

* U is a finitely generated abelian group.
* The rank of U is the number k such that U is isomorphic to torsion(U) x Z^k.
* If r₁ is the number of real embeddings, and r₂ is the number of conjugate pairs of complex embeddings,
  then n = r₁ + 2*r_2, so that the rank of U is also r₁ + r₂ - 1.




