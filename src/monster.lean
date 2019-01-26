import coxeter dvector presentation

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- The Monster group -/

/- according to: https://mathoverflow.net/questions/142205/presentation-of-the-monster-group

There's a 12-generator 80-relator presentation for the Monster group. Specifically, we have 78 relators for the Coxeter group Y443:12 relators of the form x2=1
, one for each node in the Coxeter-Dynkin diagram;
11 relators of the form (xy)3=1, one for each pair of adjacent nodes; 55 relators of the form (xy)2=1 (commutators), one for each pair of non-adjacent nodes; together with a single 'spider' relator, (ab₁c₁ab₂c₂ab₃c₃)^10=1 , which results in the group M×C2. We can get rid of the C2 by quotienting out by an eightieth relation, x=1, where x is the unique non-identity element in the centre of the group. -/ 

@[derive decidable_eq]inductive coxeter_vertices {n} (xs : dvector ℕ n) : Type
| torso : coxeter_vertices
| arm : ∀ x : dfin n, dfin (xs.nth'' x + 1) → coxeter_vertices

open coxeter_vertices

inductive coxeter_edges_directed {n} (xs : dvector ℕ n) : (coxeter_vertices xs) → (coxeter_vertices xs) → Prop 
| edge_torso : ∀ i : dfin n , coxeter_edges_directed (arm i dfin.fz) (torso _)
| edge_arm : ∀ i : dfin n, ∀ v : dfin (xs.nth'' i + 1), v ≠ dfin.last _ → coxeter_edges_directed (arm i v) (arm i (v+1)) 

inductive symmetric_closure {α : Type*} (E : α → α → Prop) : α → α → Prop
| incl : ∀ a b : α, E a b → symmetric_closure a b
| symm : ∀ a b : α, E a b → symmetric_closure b a

def coxeter_edges {n} (xs : dvector ℕ n) : coxeter_vertices xs → coxeter_vertices xs → Prop
  := symmetric_closure (coxeter_edges_directed xs)

-- TODO derive decidability instance
noncomputable instance decidable_coxeter_edges {n} (xs : dvector ℕ n) : decidable_rel $ coxeter_edges xs :=
  λ _ _, classical.prop_decidable _

noncomputable def Y443 : Group := coxeter_group $ matrix_of_graph (coxeter_edges [3,3,2])

section spider

/- coxeter_vertices [p,q,r] consists of a left arm of length p, a right arm of length q, and
a bottom arm of length r, with one node in the center connecting them.

arm i j gets the jth element of the ith arm, where both i and j start indexing from 0.
-/

def a  : Y443 := generated_of $ torso _
def b₁ : Y443 := generated_of $ arm (by to_dfin 0) (by to_dfin 0)
def c₁ : Y443 := generated_of $ arm (by to_dfin 0) (by to_dfin 1)
def b₂ : Y443 := generated_of $ arm (by to_dfin 1) (by to_dfin 0)
def c₂ : Y443 := generated_of $ arm (by to_dfin 1) (by to_dfin 1)
def b₃ : Y443 := generated_of $ arm (by to_dfin 2) (by to_dfin 0)
def c₃ : Y443 := generated_of $ arm (by to_dfin 2) (by to_dfin 1)

/- (ab₁c₁ab₂c₂ab₃c₃)^10 -/
noncomputable def spider : Y443 := (a * b₁ * c₁ * a * b₂ * c₂ * a * b₃ * c₃)^10

end spider

noncomputable def Y443_mod_spider : Group := Y443/⟪{spider}⟫

def unique_non_identity_in_center_spec : ∃! x : Y443_mod_spider, x ≠ 1 ∧ (x ∈ is_subgroup.center Y443_mod_spider) := omitted 

noncomputable def unique_non_identity_in_center : Y443_mod_spider := classical.indefinite_description _ unique_non_identity_in_center_spec

namespace Monster
noncomputable def Monster : Group := Y443_mod_spider/⟪{unique_non_identity_in_center}⟫
end Monster
