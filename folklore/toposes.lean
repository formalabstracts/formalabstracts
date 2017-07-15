-- an incomplete definition of toposes

import .categories

constant nno_structure : Type

structure natural_numbers (C : category) :=
    (underlying_object : C.obj)
    (nno_structure : nno_structure)

constant missing_topos_structure : Type

structure topos :=
    (underlying_category : category)
    (nno : natural_numbers underlying_category)
    (exponent : Π (A B : underlying_category.obj), exponential A B)
    (topos_structure : missing_topos_structure)
