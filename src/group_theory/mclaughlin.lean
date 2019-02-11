import ..data.dvector .presentation .monster

local notation `⟪`:50 a `⟫`:50 := free_group.of a
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- From the corresponding entry in the atlas (p. 100) the McLaughlin sporadic group is given by a generalized Coxeter-type presentation modulo additional relations -/

open coxeter_vertices
namespace mclaughlin

/- The graph is question is

a--b-5-c--d
 4 ↖  ↗  ↖ 4
     e -6-f

which we'll write as the annotated_graph of a Coxeter Y-diagram with the diagonal edges inserted
-/

def mclaughlin_prediagram : annotated_graph :=
  annotated_graph_of_graph $ coxeter_edges [5]

noncomputable instance : decidable_rel mclaughlin_prediagram.edge :=
  λ _ _, classical.prop_decidable _

private def a : mclaughlin_prediagram.vertex := torso
private def b : mclaughlin_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 0)
private def c : mclaughlin_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 1)
private def e : mclaughlin_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 2)
private def d : mclaughlin_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 3)
private def f : mclaughlin_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 4)

noncomputable def mclaughlin_diagram : annotated_graph :=
  insert_edge (insert_edge (insert_edge (annotate mclaughlin_prediagram (b,c) 5) (a,e) 4) (c,e) 3) (c,f) 4

noncomputable instance mclaughlin_diagram_decidable_rel : decidable_rel mclaughlin_diagram.edge :=
  λ _ _, classical.prop_decidable _

noncomputable def mclaughlin_diagram_group : Group :=
  coxeter_group $ matrix_of_annotated_graph mclaughlin_diagram

private def a : mclaughlin_diagram_group := generated_of $ a
private def b : mclaughlin_diagram_group := generated_of $ b
private def c : mclaughlin_diagram_group := generated_of $ c
private def e : mclaughlin_diagram_group := generated_of $ d
private def d : mclaughlin_diagram_group := generated_of $ d
private def f : mclaughlin_diagram_group := generated_of $ f

noncomputable def McL : Group :=
  mclaughlin_diagram_group/⟪{(c*f)^2 * a⁻¹, (e * f)^3 * b⁻¹, (e*a*b)^3, (b*c*e)^5, (a*e*c*d)^4, (c*e*f)^21, (c*e*f)^7}⟫

end mclaughlin
