import ..data.dvector .presentation
open category_theory (mk_ob)

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- The Monster group -/

/- according to: https://mathoverflow.net/questions/142205/presentation-of-the-monster-group

There's a 12-generator 80-relator presentation for the Monster group. Specifically, we have 78 relators for the Coxeter group Y443:12 relators of the form x^2=1
, one for each node in the Coxeter-Dynkin diagram;
11 relators of the form (xy)3=1, one for each pair of adjacent nodes; 55 relators of the form (xy)2=1 (commutators), one for each pair of non-adjacent nodes; together with a single 'spider' relator, (ab₁c₁ab₂c₂ab₃c₃)^10=1 , which results in the group M×C2. We can get rid of the C2 by quotienting out by an eightieth relation, x=1, where x is the unique non-identity element in the centre of the group. -/

noncomputable def Y443 : Group := coxeter_group $ matrix_of_graph (coxeter_edges [4,4,3])

namespace monster
open coxeter_vertices

/- coxeter_vertices [p,q,r] consists of a left arm of length p, a right arm of length q, and
a bottom arm of length r, with one node in the center connecting them.

arm i j gets the jth element of the ith arm, where both i and j start indexing from 0.
-/

private def a  : Y443 := generated_of torso
private def b₁ : Y443 := generated_of $ arm (by to_dfin 0) (by to_dfin 0)
private def c₁ : Y443 := generated_of $ arm (by to_dfin 0) (by to_dfin 1)
private def b₂ : Y443 := generated_of $ arm (by to_dfin 1) (by to_dfin 0)
private def c₂ : Y443 := generated_of $ arm (by to_dfin 1) (by to_dfin 1)
private def b₃ : Y443 := generated_of $ arm (by to_dfin 2) (by to_dfin 0)
private def c₃ : Y443 := generated_of $ arm (by to_dfin 2) (by to_dfin 1)

/- (ab₁c₁ab₂c₂ab₃c₃)^10 -/
noncomputable def spider : Y443 := (a * b₁ * c₁ * a * b₂ * c₂ * a * b₃ * c₃)^10

/-- The Fischer-Griess monster group -/
noncomputable def Monster : Group :=
mk_ob $ quotient_group.quotient $ is_subgroup.center $ Y443/⟪{spider}⟫

end monster
