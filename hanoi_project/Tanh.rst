
.. code-block:: lean

  def isPrime (n : ℕ) : Prop := (n ≥ 2) ∧ (∀ m: ℕ, m ≥ 1 ∧ m ∣ n → ( m = 1 ∨ m = n) )

  def infinite (s: set ℕ ): Prop := ∀ n : ℕ, ∃ m ∈ s, n < m
  

The `Twin Prime Conjecture <https://www.britannica.com/science/twin-prime-conjecture>`_
=====================
Introduction
-----------
    **Twin prime conjecture**, also known as Polignac's conjecture, in number theory, assertion that there are infinitely many twin primes, or pairs of primes that differ by 2.
    
    For example, 3 and 5, 5 and 7, 11 and 13, and 17 and 19 are twin primes.
Informal statement
------------------

preformally: ::

 There are infinitely many pairs of primes p and p+2.

Formal statement
----------------

.. code-block:: lean 

 theorem TwicePrimeConjecture : infinite {n : ℕ  | isPrime n → isPrime (n + 2) ∨ isPrime (n - 2)} := sorry


The `Goldbach’s Conjecture <https://artofproblemsolving.com/wiki/index.php?title=Goldbach_Conjecture>`_
=====================
Introduction
-----------
    **The Goldbach Conjecture** is a yet unproven conjecture stating that every even integer greater than two is the sum of two prime numbers. The conjecture has been tested up to 400,000,000,000,000. 
    
    **Goldbach's conjecture** is one of the oldest unsolved problems in number theory and in all of mathematics.
 
Informal statement
------------------

preformally: ::

 Every even positive integer greater than 2 can be written as the sum of two primes

Formal statement
----------------

.. code-block:: lean 

 theorem Goldbach'sConjecture : ∀ n : ℕ, n > 2 ∧ 2 ∣ n  → ∃ a b : ℕ, isPrime a ∧ isPrime b ∧ n = a + b := sorry

The `Polignac Conjecture <https://en.wikipedia.org/wiki/Polignac%27s_conjecture>`_
=======================
Introduction
-----------
    In number theory, **Polignac's conjecture** was made by Alphonse de Polignac in 1849 and states:
     For any positive even number n, there are infinitely many prime gaps of size n. In other words: There are infinitely many cases of two consecutive prime numbers with difference n.
    
Informal statement
------------------

preformally: ::

 For every even number 2n, there are infinitely many pairs of consecutive primes which differ by 2n.

Formal statement
----------------

.. code-block:: lean 

theorem PolignacConjecture :∀ n : ℕ, 2 ∣ n → infinite { a |isPrime a  →  isPrime (a + n) ∨ isPrime (a - n)} := sorry

The `Opperman Conjecture <https://en.wikipedia.org/wiki/Oppermann%27s_conjecture>`_
=======================
Introduction
-----------
    Oppermann's conjecture is an unsolved problem in mathematics on the distribution of prime numbers.
    It is closely related to but stronger than Legendre's conjecture, Andrica's conjecture, and Brocard's conjecture.
    It is named after Danish mathematician Ludvig Oppermann, who posed it in 1882.
Informal statement
------------------

preformally: ::

 There always a prime between n^2 and (n+1)^2.

Formal statement
----------------

.. code-block:: lean 
 
 theorem OppermanConjecture : ∀ n : ℕ, ∃ a : ℕ, isPrime a ∧ n^2 < a ∧ a < (n + 1)^2 := sorry
