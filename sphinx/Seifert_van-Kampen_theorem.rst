Seifert van-Kampen theorem
--------------------------

This article gives a formal statement of the Seifert van-Kampen theorem.  For Wikipedia's
description, see `Seifert van-Kampen theorem`_. There a more general theorem for
groupoids is also describd.

Informal statement
   
   Let X be a topological space which is the union of two open and
   path connected subspaces U₁, U₂. Suppose U₁ ∩ U₂ is path connected
   and nonempty, and let x₀ be a point in U₁ ∩ U₂ that will be used as
   the base of all fundamental groups. The inclusion maps j₁ and j₂ of
   U₁ and U₂ into X induce group homomorphisms j₁ : π₁(U₁,x₀) →
   π₁(X,x₀) and j₂ : π₁(U₂,x₀) → π₁(X,x₀). Then X is path connected
   and j₁ and j₂ form a commutative pushout diagram: that is, the
   fundamental group of X is the free amalgamated product of the
   fundamental groups of U₁ and U₂ over π₁ (U₁ ∩ U₂ , x₀ ).

.. code-block:: text
  
  notation:
  (X : topological_space)
  (U₁ : path-connected, open, subset X)
  (U₂ : path-connected, open, subset X)
  (_  : path_connected (U₁ ∩ U₂))
  (x₀ ∈ U₁ ∩ U₂)
  (j₁ := fundamental_group_functor (inclusion (U₁,x₀) (X,x₀)))
  (j₂ := fundamental_group_functor (inclusion (U₂,x₀) (X,x₀)))
  (i₁ := fundamental_group_functor (inclusion (U₁ ∩ U₂,x₀) (U₁,x₀)))
  (i₂ := fundamental_group_functor (inclusion (U₁ ∩ U₂,x₀) (U₂,x₀)))

  theorem Seifert-van_Kampen :=
  is_group_pushout (i₁,i₂) (j₁,j₂)

Notes.

* The theorem has been `formalized in HoTT <https://home.sandiego.edu/~shulman/papers/vankampen.pdf>`_.
* The theorem is naturally expressed visually as pushout diagram.



