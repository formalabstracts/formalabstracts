Puiseux's theorem
-----------------

This article gives a formal statement of Puiseux's theorem.  For Wikipedia's
description, see
`Puiseux series <https://en.wikipedia.org/wiki/Puiseux_series>_`.

informally

Let ``K`` be an algebraically closed field of characteristic zero.
The field of Puiseux series over ``K`` is an algebraic closure of the
field of formal Laurent series over ``K``.

preformally

.. code-block:: text

  notation:
  (K : characteristic 0, algebraically_closed, field)
  (Kt := field_of_Puiseux_series_over K)
  (Lt := Laurent_subfield Kt 1)

  theorem Puiseux :=
  (algebraic_closure Lt Kt)

  
Notes
=====
* The same wiki page defines the Puiseux series as a
  direct limit of fields of formal Laurent series, indexed by m ≥ 1.
  ``Lt`` is the lowest level embedding.  
