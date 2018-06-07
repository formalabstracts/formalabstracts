Unit group of a ring
--------------------

This article gives a formal definition of the unit group of a ring.  For Wikipedia's
description, see `unit (ring theory) <https://en.wikipedia.org/wiki/Unit_(ring_theory)>`_.

informally

  Let R be a ring.
  The set of elements u in R such that there exists a two-sided
  inverse v:  ``u*v = v*u = 1`` forms a group U(R) with binary operation ``*``.  The group is
  called the group of units of R.  

preformally: ::

  notation:
  (R : ring)
  (unit R := { u ∈ R // ∃ v ∈ R, u*v = v*u = 1})

  definition:
  (unit_group R :=
   {type     := unit R;
   ( * ) u v := u * v;
   _         := !;
   } : group)

  propositional-penumbra:
  (commutative R) → (abelian U(R))
