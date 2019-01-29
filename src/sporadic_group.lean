import .basic monster
open monster

/- the first happy family, a.k.a. Mathieu groups -/
/-- the Mathieu group M₁₁ -/
def M11 : Group := sorry
/-- the Mathieu group M₁₂ -/
def M12 : Group := sorry
/-- the Mathieu group M₂₂ -/
def M22 : Group := sorry
/-- the Mathieu group M₂₃ -/
def M23 : Group := sorry
/-- the Mathieu group M₂₄ -/
def M24 : Group := sorry

/- the second happy family -/
/-- the Conway group Co₁ -/
def Co1 : Group := sorry
/-- the Conway group Co₂ -/
def Co2 : Group := sorry
/-- the Conway group Co₃ -/
def Co3 : Group := sorry
/-- the McLaughlin group -/
def McL : Group := sorry
/-- the Higman–Sims group -/
def HS : Group := sorry
/-- the Janko group J₂ -/
def J2 : Group := sorry
/-- the Suzuki sporadic group	-/
def Suz : Group := sorry

/- THE THIRD HAPPY FAMILY -/

-- todo: move monster here

/-- The baby monster group B is defined as follows:
if x be any element in conjugacy class 2A, 
then the centralizer C_M(x) is 2 ⬝ B, so B ≅ C_M(x)/Z(C_M(x)) -/
noncomputable def BabyMonster : Group :=
let C := conj_class Monster 2 'A' in
let x := classical.some C.1.2 in
let Cx : set Monster := centralizer {x} in
category_theory.mk_ob $ quotient_group.quotient $ is_subgroup.center $ Cx

/-- The Fischer group Fi24 -/
-- remark on notation: according to Wikipedia is written Fi₂₄ or F₂₄'. Tom denotes it as Fi24' and sometimes without a prime as Fi24 (assuming that he means the same group)
noncomputable def Fi24' : Group := 
let C := conj_class Monster 3 'A' in
let x := classical.some C.1.2 in
let Cx : set Monster := centralizer {x} in
category_theory.mk_ob $ quotient_group.quotient $ is_subgroup.center $ Cx

/-- the Fischer group Fi23 -/
def Fi23 : Group := sorry
/-- the Fischer group Fi22 -/
def Fi22 : Group := sorry
/-- the Thompson Group -/
noncomputable def Th : Group :=
let C := conj_class Monster 3 'C' in
let x := classical.some C.1.2 in
let span_x : set Monster := group.closure {x} in
let C_span_x : set Monster := centralizer span_x in
let span_x' : set C_span_x := subtype.val ⁻¹' span_x in
by { haveI : normal_subgroup span_x' := omitted,
     exact category_theory.mk_ob (quotient_group.quotient span_x') }

/-- the Harada–Norton group	-/
def HN : Group := sorry
/-- the Held group -/
def He : Group := sorry

/- the pariahs  -/
/-- the Janko group J₁ -/
def J1 : Group := sorry
/-- the Janko group J₃ -/
def J3 : Group := sorry
/-- the Lyons group -/
def Ly : Group := sorry
/-- the O'Nan group	-/
def O'N : Group := sorry
/-- the Janko group J₄ -/
def J4 : Group := sorry
/-- the Rudvalis group -/
def Ru : Group := sorry
