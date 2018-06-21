Green-Tao theorem
-----------------

This article gives a formal statement of the Green-Tao theorem.  For Wikipedia's
description, see
`Green-Tao theorem <https://en.wikipedia.org/wiki/Green%E2%80%93Tao_theorem>`_.

Informal statement

    Let π ( N ) denote the number of primes less than or equal to N. If A is a subset of the prime numbers such that

    lim sup N → ∞ card( A ∩ [ 1 , N ] ) / π ( N ) > 0,

    then for all positive integers k, the set A contains infinitely many increasing arithmetic progressions of length k.

.. code-block:: text

  notation:
  (π (N) := card { p : prime, ℕ | p ≤ N})
  (A : subset (prime, ℕ))
  (positive_density : limsup N ∞ (card (A ∩ [1,N]) / π (N)) > 0)
  (k : positive, ℕ)

  theorem Green-Tao :=
  infinite (increasing, arithmetic_progression, length k, list (subtype A) )
  
Notes
=====

