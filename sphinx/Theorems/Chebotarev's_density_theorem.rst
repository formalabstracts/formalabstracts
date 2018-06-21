Chebotarev's density theorem
----------------------------

This article gives a formal statement of the Chebotarev density theorem.  For Wikipedia's
description, see
`Chebotarev density theorem <https://en.wikipedia.org/wiki/Chebotarev%27s_density_theorem>`_.

Informal statement

  Let L be a finite Galois extension of a number field K
  with Galois group G.
  Let C be a conjugacy class in G.
  The set of primes v of K that do not divide the relative discriminant of K/L and
  whose associated Frobenius conjugacy class Fv
  is C has density
  # C / # G . 

.. code-block:: text

  notation:
  (K : number field)
  (L : extension K, number field)
  (_ : Galois_field_extension K L)
  (G := Galois_group K L)
  (C : conjugacy_class, subset G)

  theorem_Chebotarev_density_theorem:=

  dirichlet_density
  { v : prime K | not (divide v (relative_discriminant L K)) ∧
  Frobenius v L K = C }
  = card C / card G.


Definition Links
================

* Number field means algebraic number field.

* Wiki is stated for a finite union of conjugacy, but by the finite additivity of both sides,
  the Wiki version follows for the version here, which is a single conjugacy class.
  
* The Frobenius refers to `Frobenius for global fields
  <https://en.wikipedia.org/wiki/Frobenius_endomorphism>`_.  It is a
  conjugacy class in the Galois group, but many writers identify it with
  an arbitrary choice in that conjugacy class.

* prime means a prime ideal in the ring of integers of K.
  
* The density refers to `analytic density
  <https://en.wikipedia.org/wiki/Dirichlet_density>`_ as in
  `Lenstra's note <http://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf>`_.
  (Wikipedia has been updated.)

* The
  Dirichlet density is a non-negative real number.  The right-hand
  side of the theorem is a rational number.
  
* Ramification refers to `ramification in algebraic number theory
  <https://en.wikipedia.org/wiki/Ramification_(mathematics)>`_.  Note
  that ramification is a relative notion that refers to both L and K.
  It is easier to test ramification in terms of the `relative discriminant of L/K
  <https://en.wikipedia.org/wiki/Discriminant_of_an_algebraic_number_field>`_,
  as explained in Lenstra's notes, but the notion of divisibility of primes is needed.
  In some sense this is all irrelevant, because there are only finitely many primes,
  and the density is insensitive to finite sets.


**Application.**

Let f(x) = x^n + a x^{n-1} + ...
be an irreducible polynomial of degree n with integer coefficients.
Suppose that the Galois group of the splitting field of f is the symmetric group on n letters.

For every prime number p, we can factor f(x) modulo into irreducible factors
f_1 (x) f_2(x) .... f_n(x).  Each f_i(x) is a polynomial with coefficients in the finite field Z/pZ.
The factorization of f determines a partition of n,
given by the the degrees n_i of the factors f_i.   This procedure assigns a partition
of n to each prime p. The Chebotarev density theorem implies that the partition lambda
is obtained for a set of primes of density #C_λ/n!, where #C_λ is the number of permutations
with cycle type lambda.


