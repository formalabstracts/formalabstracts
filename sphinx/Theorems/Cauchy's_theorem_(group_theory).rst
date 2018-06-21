Cauchy's theorem (group theory)
-------------------------------

This article gives a formal statement of the Cauchy's theorem in group theory.  For Wikipedia's
description, see
`Cauchy's theorem <https://en.wikipedia.org/wiki/Cauchy%27s_theorem_(group_theory)>`_.

Informal statement

   Let G be a finite group and p be a prime. If p divides the order of G, then G has an element of order p.

.. code-block:: text

  notation:
  (G : finite, group)
  (p : prime, ℕ)

  theorem Cauchy's_theorem_group_theory :=
  (p | card G) → (∃ x ∈ G, ord x = p)
