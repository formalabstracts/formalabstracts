.. Twin prime conjecture

Twin prime conjecture
=====================

Introduction
------------
The `twin prime conjecture <https://en.wikipedia.org/wiki/Twin_prime#History>`_ states that there exist infinitely many primes :math:`p` such that :math:`p + 2` is also prime.


Formal statement
----------------

.. code-block:: lean

		import data.set.finite

		import data.nat.prime

		theorem Twin_prime_conjecture : set.infinite {p : ℕ | (nat.prime p) ∧ (nat.prime (p+2))} := sorry
	
