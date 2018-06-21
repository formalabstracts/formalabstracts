Brouwer fixed-point theorem
---------------------------

This article gives a formal statement of the Brouwer fixed-point theorem.  For Wikipedia's
description, see `Brouwer fixed-point theorem <https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem>`_

Informal statement
   
   Let K be a topological space that is homeomorphic
   to a closed ball in Euclidean space.
   Then every [continuous] [function] f from K to itself
   has a fixed point.

.. code-block:: text
  
  notation:
  (K : topological space)
  (f : continuous, function K K)
  (n : ℕ)

  theorem Brouwer_fixed-point_theorem :=
  if there exists
  (B : closed_ball, homeomorphic K, subset (Euclideanⁿ))
  then there exists (p ∈ K), f p = p.

Notes.

* Here Euclidean space is considered as a metric space with the
  Euclidean metric.  Its structure as a vector space is not needed.

* A general form of the Brouwer fixed-point theorem based on the
  Lefschetz fixed-point theorem can be found in `Belk's stack exchange
  comment <https://math.stackexchange.com/a/423304>`_.

* This theorem (for compact convex sets)
  has been `formalized in HOL Light <http://www.cl.cam.ac.uk/~jrh13/papers/neworleans.pdf>`_.

