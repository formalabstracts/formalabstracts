Brouwer fixed-point theorem
---------------------------

This article gives a formal statement of the Brouwer fixed-point theorem.  For Wikipedia's
description, see `Brouwer fixed-point theorem <https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem>`_

informally 
   
   Theorem Brouwer fixed-point theorem :=
   Let K be a topological space that is homeomorphic
   to a closed ball in Euclidean space.
   Then every [continuous] [function] f from K to itself
   has a fixed point.

preformally: ::
  
  notation:
  (K : topological space)
  (f : continuous, function K K)
  (n : ℕ)

  theorem Brouwer_fixed-point_theorem :=
  if there exists
  (B : closed_ball, homeomorphic K, subset (Euclideanⁿ))
  then there exists (p ∈ K), f p = p.

Notes. Here Euclidean space is considered as a metric space with the Euclidean metric.
Its structure as a vector space is not needed.



