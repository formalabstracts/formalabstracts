Infinitude of Primes
--------------------

This article gives a formal statement of Infinitude of Primes.  For Wikipedia's
description, see
`Infinitude of Primes <https://en.wikipedia.org/wiki/Prime_number#Infiniteness>`_.

Informally statement
  There are infinitely many :ref:`prime` numbers.


Formally statement::

  import data.nat.prime data.set.finite
    
  theorem Infinitude_of_Primes : set.infinite { p:ℕ | nat.prime p} := sorry

  
