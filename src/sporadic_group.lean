import .basic monster
open monster

/- the first happy family, a.k.a. Mathieu groups -/
def M11 : Group := sorry
def M12 : Group := sorry
def M22 : Group := sorry
def M23 : Group := sorry
def M24 : Group := sorry

/- the second happy family -/
def Co1 : Group := sorry
def Co2 : Group := sorry
def Co3 : Group := sorry
def McL : Group := sorry
def HS : Group := sorry
def J2 : Group := sorry
def Suz : Group := sorry

/- THE THIRD HAPPY FAMILY -/

-- todo: move monster here

/- the baby monster -/
noncomputable def twoB : Group :=
let C := conj_class Monster 2 'A' in
let x := classical.some C.1.2 in
category_theory.mk_ob (@centralizer Monster _ {x})

lemma unique_non_identity_in_center_twoB_spec : ∃! x : twoB, x ≠ 1 ∧ x ∈ is_subgroup.center twoB := 
omitted 

noncomputable def unique_non_identity_in_center_twoB : twoB := 
classical.some unique_non_identity_in_center_twoB_spec

/-- The baby monster group -/
noncomputable def BabyMonster : Group := twoB/⟪{unique_non_identity_in_center_twoB}⟫

/- Fi24' -/
noncomputable def threeFi24' : Group :=
let C := conj_class Monster 3 'A' in
let x := classical.some C.1.2 in
category_theory.mk_ob (@centralizer Monster _ {x})

lemma non_identity_in_center_threeFi24'_spec : 
  ∃ x : threeFi24', x ≠ 1 ∧ x ∈ is_subgroup.center threeFi24' := 
omitted 

noncomputable def unique_non_identity_in_center_threeFi24' : threeFi24' := 
classical.some non_identity_in_center_threeFi24'_spec

/-- The Fischer group Fi24 -/
-- remark on notation: according to Wikipedia is written Fi₂₄ or F₂₄'. Tom denotes it as Fi24' and sometimes without a prime as Fi24 (assuming that he means the same group)
noncomputable def Fi24' : Group := threeFi24'/⟪{unique_non_identity_in_center_threeFi24'}⟫

def Fi23 : Group := sorry
def Fi22 : Group := sorry
def Th : Group := sorry
def HN : Group := sorry
def He : Group := sorry

/- the pariahs -/
def J1 : Group := sorry
def J3 : Group := sorry
def Ly : Group := sorry
def O'N : Group := sorry
def J4 : Group := sorry
def Ru : Group := sorry
