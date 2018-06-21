Infinitude of Primes
====================

This article gives a formal statement of Infinitude of Primes.  For Wikipedia's
description, see
`Infinitude of Primes <https://en.wikipedia.org/wiki/Prime_number#Infiniteness>`_.

Informal statement
------------------

  The theorem states that there are infinitely many :ref:`prime` numbers.


Preformal statement
-------------------

  Prime number

  (p: ℕ) p is prime if p ≥ 2 ∧ m | p, m = 1 ∨ m = p 
  
  Infinite set 
  
  (s : set ℕ) s is an infinite set if ∀ n : ℕ, ∃ m ∈ s, n < m


Formal statement 
----------------

.. code-block:: lean 

  import data.nat.prime data.set.finite
    
  theorem Infinitude_of_Primes : set.infinite { p:ℕ | nat.prime p} := sorry
