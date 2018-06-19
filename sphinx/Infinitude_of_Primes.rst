Infinitude of Primes
--------------------

This article gives a formal statement of Infinitude of Primes.  For Wikipedia's
description, see
`Infinitude of Primes <https://en.wikipedia.org/wiki/Prime_number#Infiniteness>`_.

Informally statement

  There are infinitely many :ref:`prime` numbers.


Preformally ::

  Prime number

  (p: ℕ) p is prime if p ≥ 2 ∧ m | p, m = 1 ∨ m = p 
  
  Infinite set 

  (s : set ℕ) s is an infinite set if ∀ n : ℕ, ∃ m ∈ s, n < m


Formally statement::
  
  import data.nat.prime data.set.finite
    
  theorem Infinitude_of_Primes : set.infinite { p:ℕ | nat.prime p} := sorry

  
