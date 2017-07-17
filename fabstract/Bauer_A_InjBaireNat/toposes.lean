-- an incomplete definition of toposes

import meta_data
       .categories

run_cmd tactic.skip -- temporary fix

constant nno_structure : Type

structure natural_numbers (C : category) :=
    (underlying_object : C.obj)
    (nno_structure : nno_structure)

unfinished missing_topos_structure : Type :=
  { description := "the rest of the structure of an elementary topos",
    cite := [] }

structure topos :=
    (underlying_category : category)
    (nno : natural_numbers underlying_category)
    (exponent : Π (A B : underlying_category.obj), exponential A B)
    (topos_structure : missing_topos_structure)
