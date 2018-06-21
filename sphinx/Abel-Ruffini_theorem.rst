Abel-Ruffini theorem
--------------------

This article gives a formal statement of Abel-Ruffini theorem.  For Wikipedia's
description, see
`Abel-Ruffini theorem <https://en.wikipedia.org/wiki/Abel%E2%80%93Ruffini_theorem>`_.

*This article is a stub. You can improve it by completing
the formal abstract.*

informally

  For every `n ≥ 5` there exists a polynomial of degree n with
  rational coefficients whose splitting field is not a solvable extension
  of ℚ

preformally

.. code-block:: none
  
  (n : ℕ)
  (_ : n ≥ 5)
  
  ∃ p ∈ ℚ[x], ∃ K, splitting_field p K ℚ ∧ degree p = n ∧
  ¬ (solvable, field_extension K ℚ).
  
formally

.. code-block:: lean

  --INSERT

Note:
=====

* The splitting field is only defined up to isomorphism over `K`.

* The precise meaning of 'solvable in radicals' is captured by the solvability
  of `K/ℚ`.

