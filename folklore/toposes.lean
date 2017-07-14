-- an incomplete definition of toposes

import .categories

structure natural_numbers (C : category) :=
  mk_natural_number_object ::
    (nno_object : C.obj)
    (nno_structure : Type)

-- an incomplete definition of toposes
-- this should probably be done using type classes
structure topos :=
  mk_topos ::
    (underlying_category : category)
    (nno : natural_numbers underlying_category)
    (other_structure_missing : Type)

structure real_numbers (T : topos) :=
  mk_real_numbers_object ::
    (reals_object : T.underlying_category.obj)
    (reals_structure : Type)

-- every topos has a real-numbers object
axiom dedekind_reals : ∀ (T : topos), real_numbers T
