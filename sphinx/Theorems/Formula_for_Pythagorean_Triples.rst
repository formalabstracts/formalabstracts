Formula for Pythagorean Triples
===============================

This article gives a formal statement of Formula for Pythagorean Triples.  For Wikipedia's
description, see
`Formula for Pythagorean Triples <https://en.wikipedia.org/wiki/Pythagorean_triple>`_.


Informally
----------

  A Pythagorean triple consists of three positive integers :math:`a`, :math:`b`, and :math:`c`, such that :math:`a^2 + b^2 = c^2`. 
  If :math:`(a, b, c)` is a Pythagorean triple, then so is :math:`(ka, kb, kc)` for any positive integer :math:`k`. 
  A primitive Pythagorean triple is one in which :math:`a`, :math:`b` and :math:`c` are coprime.

Preformally
-----------
  (a b c: ℕ)

  :math:`(a, b, c)` is a Pythagorean triple if :math:`c^2 = a^2 + b^2`.

  If :math:`(a, b, c)` is a Pythagorean triple then ∀ k: ℕ, :math:`(k*a)^2 + (k*b)^2 = (k*c)^2`.

  A primitive Pythagorean triple

  :math:`(a, b, c)` is a primitive Pythagorean triple if :math:`(a, b, c)` is a Pythagorean triple and a, b and c are coprime.

  Euclid's formula

  :math:`(a, b, c)` is a primitive Pythagorean triple ↔ ∃ m n : ℕ, :math:`m > n > 0` such that 
  m and n are coprime and not both odd and :math:`a = m^2 - n^2`, :math:`b = 2mn` and :math:`c = m^2 + n^2`.
  

Formally
--------
.. code-block:: lean

  open nat

  def is_odd (a : nat) := ¬ ∃ b, a = 2*b 

  def both_odd (m n: nat) := is_odd m ∧ is_odd n 

  theorem Pythagorean_Triple_Theorem (a b c: ℕ) (h: a*a + b*b = c*c) (h1: coprime a b ∧ coprime a c ∧ coprime b c):
    (∀ k: ℕ, (k*a)^2 + (k*b)^2 = (k*c)^2) ∧ (∃ m n : ℕ, ¬ both_odd m n ∧ coprime m n ∧ m > n ∧ a = m^2 - n^2 ∧  b = 2*m*n ∧ c = m^2 + n^2)
    := sorry

