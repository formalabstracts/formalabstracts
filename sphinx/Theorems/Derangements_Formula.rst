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

Formal statement
----------------

.. code-block:: lean

    import data.fintype

    def symm_group (α : Type) := { f : α → α | function.bijective f}

    def derangement (α : Type) : symm_group α → Prop
    := (λ f , (∀ x : α, (subtype.val f) x ≠ x))

    instance (α : Type) : fintype ({f : symm_group α // derangement α f}) := sorry

    theorem derangements_formula (α : Type) [fintype α]: ∀ n : ℕ, fintype.card α = n → (fintype.card {f : symm_group α // derangement α f} : int)
    = (nat.fact n) * ((list.range (n+1)).map (λ k : ℕ, (-(1 : int) ^ k)/(nat.fact k))).sum := sorry
