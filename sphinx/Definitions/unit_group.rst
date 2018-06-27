Unit group of a monoid (or ring)
--------------------------------

This article gives a formal definition of the unit group of a monoid.  For Wikipedia's
description, see `unit (ring theory) <https://en.wikipedia.org/wiki/Unit_(ring_theory)>`_.

Informal statement

  Let M be a monoid.
  The set of elements u in M such that there exists a two-sided
  inverse v:  ``u*v = v*u = 1`` forms a group U(M) with binary operation ``*``.  The group is
  called the group of units of M.  

.. code-block:: text

  notation:
  (M : monoid)
  (unit M := { u ∈ M // ∃ v ∈ M, u*v = v*u = 1})

  def unit_group (M : monoid) : group :=
   {type     := unit M; ( * ) u v := u * v; _ := ! }

  propositional-penumbra:
  (abelian M) → (abelian U(M))

Notes
=====

  * The unit group of a ring is the unit group of the underlying multiplicative monoid.
    
