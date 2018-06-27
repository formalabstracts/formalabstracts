Borsuk-Ulam theorem
-------------------

This article gives a formal statement of the Borsuk-Ulam theorem.
For Wikipedia's description, see
`Borsuk-Ulam theorem <https://en.wikipedia.org/wiki/Borsuk-Ulam_theorem>`_.


Informal statement

if f : S^n → R^n is continuous then there exists an
x ∈ S^n  such that: f ( − x ) = f ( x ).


.. code-block:: text

  notation:
  (n : ℕ)
  (_ : n ≥ 1)
  (f : continuous, function (sphereⁿ) (Euclideanⁿ))

  theorem Borsuk-Ulam :=
  ∃ x, f( -x ) = x.

Notes
=====

* Here the sphere is the unit sphere in Euclidean space.
  

