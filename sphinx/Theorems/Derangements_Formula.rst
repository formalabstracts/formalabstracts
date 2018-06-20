Derangements Formula
=======================

Introduction
------------

This article gives a formal statement of the Derangements Formula.
For Wikipedia's description, see `Derangements Formula <https://en.wikipedia.org/wiki/Derangement>`_.

*This article is a stub. You can improve it by completing the formal abstract.*

Informal statement
------------------
A **derangement** on a set :math:`X` is a permutation :math:`\sigma : X \to X` with no fixed points: for every :math:`x \in X`, :math:`\sigma(x) \neq x`.

The Derangements Formula counts the number of derangements on a finite set. Given a set :math:`X` with :math:`\#X = n`, the number of derangements on :math:`X` is given by:

.. math::

       n! \sum_{k = 0}^n \dfrac{(-1)^k}{k!}.
       


Preformal statement (temporary)
+++++++++++++++++++++++++++++++

.. code-block:: text
    
		preformal statement goes here

Formal statement
----------------

.. code-block:: lean

    -- formal abstract goes here
    constant p : ℕ → Prop

    theorem Theorem_Name : ∃ x : ℕ, p x := sorry
