Pythagorean Theorem
===================

This article gives a formal statement of Pythagorean Theorem.  For Wikipedia's
description, see
`Pythagorean Theorem <https://en.wikipedia.org/wiki/Pythagorean_theorem>`_.

Informal statement
------------------

  The theorem states that the square of the hypotenuse (the side opposite the right angle) is equal to the sum of the squares of the other two sides. 
  The theorem can be written as an equation relating the lengths of the sides :math:`a`, :math:`b` and :math:`c`, often called the "Pythagorean equation":
  .. math:: 
  `a^2 + b^2 = c^2`
  where :math:`c` represents the length of the hypotenuse and :math:`a` and :math:`b` the lengths of the triangle's other two sides.

Preformal statement
-------------------
  (α :Type) (n: ℕ) 

  (a b : vector α n) 
  
  Inner product of vector a and b 

  ⟨a,b⟩ = ∑ aᵢ*bᵢ with i = {1...n}.

  Vectors a and b are orthogonal if ⟨a,b⟩ = 0.

  If a and b are orthogonal then a and b represent two sides of right angle 
  and vertor (a + b) represent the hypotenuse.

  Norm of vector a  

  |a| = sqrt(∑ aᵢ*aᵢ) with i = {1...n}. 

  Therefore, the Pythagorean theorem can be formulated by

  |a + b|^2 = |a|^2 + |b|^2.


  
Formal statement
-----------------
.. code-block:: lean 

  def sum_list {α : Type} [has_add α][has_zero α] : list α → α
  | [] := 0
  | (a :: s) := a + sum_list s 

  def inner_product_vec {α :Type} [has_add α] [has_mul α] [has_zero α] {n:ℕ} (v1 v2 : vector α n)
  := let w:= vector.map₂ (λ x y:α, x*y) v1 v2 in sum_list w.to_list

  def add_vec {α : Type} [has_add α] {n : ℕ} ( v1 v2 : vector α n) 
  := vector.map₂ (λ a b : α, a + b) v1 v2

  notation u `+` v := add_vec u v 

  def square_of_norm_vec {α : Type} [has_mul α] [has_zero α] [has_add α] {n : ℕ} (v: vector α n)
  := let w:= vector.map (λ x:α, x*x) v in (sum_list w.to_list) 
  
  theorem Pythegorean_Theorem {α:Type} [has_add α] [has_mul α] [has_zero α]
  {n:ℕ} ( a b : vector α n) (h: inner_product_vec a b = 0) : 
  square_of_norm_vec (a + b) = square_of_norm_vec a + square_of_norm_vec b := sorry

