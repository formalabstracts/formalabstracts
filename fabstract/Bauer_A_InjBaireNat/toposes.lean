-- an incomplete definition of toposes

import meta_data
       .categories

run_cmd tactic.skip -- temporary fix

unfinished nno_structure : category → Type :=
  { description := "natural numbers object in a category",
    sources     := [cite.Website "https://ncatlab.org/nlab/show/natural+numbers+object"] }

structure natural_numbers (C : category) :=
    (underlying_object : C.obj)
    (nno_structure : nno_structure C)

unfinished missing_topos_structure : Type :=
  { description := "the rest of the structure of an elementary topos",
    sources     := [cite.Website "https://ncatlab.org/nlab/show/topos"] }

structure topos :=
    (underlying_category : category)
    (nno : natural_numbers underlying_category)
    (exponent : Π (A B : underlying_category.obj), exponential A B)
    (topos_structure : missing_topos_structure)
