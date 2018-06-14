.. Twin prime conjecture

Twin prime conjecture
=====================

Introduction
------------
The `twin prime conjecture <https://en.wikipedia.org/wiki/Twin_prime#History>`_ states that there exist infinitely many primes :math:`p` such that :math:`p + 2` is also prime.


Formal statement
----------------

.. code-block:: lean

		definition isInfinite (s : set ℕ) : Prop
		:= ∀ k : ℕ, ∃ k' ∈ s, k' > k

		definition isPrime (p : ℕ) : Prop
		:= p ≥ 2 ∧ (∀ k, k ∣ p → (k = 1 ∨ k = p))

		theorem twin_primes_conjecture : isInfinite {p : ℕ | (isPrime p) ∧ (isPrime (p+2))}
		:= sorry

