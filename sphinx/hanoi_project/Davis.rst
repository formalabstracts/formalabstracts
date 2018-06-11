.. Rudimentary article template

The Twin Prime Conjecture
=====================
Introduction
-----------
    **Twin prime conjecture**, also known as Polignac's conjecture, in number theory, assertion that there are infinitely many twin primes, or pairs of primes that differ by 2. [#twin]_
    
    For example, 3 and 5, 5 and 7, 11 and 13, and 17 and 19 are twin primes.
Informal statement
------------------

preformally: ::

 There are infinitely many pairs of primes p and p+2.

Formal statement
----------------

.. code-block:: lean 

 def twin_primes : Prop := ∀ n, ∃ p > n, isPrime p ∧ isPrime (p + 2)


The Goldbach’s Conjecture
=====================
Introduction
-----------
    **The Goldbach Conjecture** is a yet unproven conjecture stating that every even integer greater than two is the sum of two prime numbers. The conjecture has been tested up to 400,000,000,000,000. 
    
    **Goldbach's conjecture** is one of the oldest unsolved problems in number theory and in all of mathematics. [#Goldbach]_

:math::

 4 = 2 + 2

 6 = 3 + 3

 8 = 3 + 5

 10 = 3 + 7 = 5 + 5

 12 = 5 + 7

 14 = 3 + 11 = 7 + 7 etc.
 
Informal statement
------------------

preformally: ::

 Every even positive integer greater than 2 can be written as the sum of two primes

Formal statement
----------------

.. code-block:: lean 

 def Goldbach : Prop := ∀ n > 2, isEven n → ∃ p q, isPrime p ∧ isPrime q ∧ n = p + q

The Polignac Conjecture
=======================
Introduction
-----------
    In number theory, **Polignac's conjecture** was made by Alphonse de Polignac in 1849 and states:
     For any positive even number n, there are infinitely many prime gaps of size n. In other words: There are infinitely many cases of two consecutive prime numbers with difference n. [#polignac]_
    
Informal statement
------------------

preformally: ::

 For every even number 2n, there are infinitely many pairs of consecutive primes which differ by 2n.

Formal statement
----------------

.. code-block:: lean 

 def Polignac :Prop := ∀ n, ∃p > n, ∀ m, isPrime m → (m = p ∨ m = (p + 2*n))

The Opperman Conjecture
=======================
Introduction
-----------
    Oppermann's conjecture is an unsolved problem in mathematics on the distribution of prime numbers.
    It is closely related to but stronger than Legendre's conjecture, Andrica's conjecture, and Brocard's conjecture.
    It is named after Danish mathematician Ludvig Oppermann, who posed it in 1882. [#Oppermann]_
Informal statement
------------------

preformally: ::

 There always a prime between n^2 and (n+1)^2.

Formal statement
----------------

.. code-block:: lean 
 
 def Opperman :Prop := ∀ m :ℕ, isPrime m → ∃ n, m ≥ n^2 ∧ m ≤ (n+1)^2
 

.. [#twin] https://www.britannica.com/science/twin-prime-conjecture
.. [#Goldbach] https://artofproblemsolving.com/wiki/index.php?title=Goldbach_Conjecture
.. [#polignac] https://en.wikipedia.org/wiki/Polignac%27s_conjecture
.. [#Oppermann] https://en.wikipedia.org/wiki/Oppermann%27s_conjecture