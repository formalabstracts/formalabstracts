import ..data.dvector .presentation .monster .euclidean_lattice

local notation `⟪`:50 a `⟫`:50 := free_group.of a
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- We define the Conway groups. Except for Co1, which is constructed as a quotient of the
  automorphism group of the Leech lattice, the Conway groups Co2 and Co3 admit general
  Coxeter-type presentations modulo additional relations (p. 134 and  in the atlas)-/

open coxeter_vertices
namespace conway_groups

noncomputable def Co1 : Group :=
  category_theory.mk_ob $ quotient_group.quotient $ is_subgroup.center $ lattice_Aut Λ_24


section Co2
def Co2_prediagram : annotated_graph :=
  annotated_graph_of_graph $ coxeter_edges [1,1,3,1]

instance Co2_prediagram_decidable_eq : decidable_eq Co2_prediagram.vertex :=
  by apply_instance

noncomputable instance Co2_prediagram_decidable_rel : decidable_rel Co2_prediagram.edge :=
  λ _ _, classical.prop_decidable _

private def a : Co2_prediagram.vertex := arm (by to_dfin 2) (by to_dfin 1)
private def b : Co2_prediagram.vertex := arm (by to_dfin 2) (by to_dfin 2)
private def c : Co2_prediagram.vertex := arm (by to_dfin 1) (by to_dfin 0)
private def d : Co2_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 0)
private def e : Co2_prediagram.vertex := arm (by to_dfin 2) (by to_dfin 0)
private def f : Co2_prediagram.vertex := torso
private def g : Co2_prediagram.vertex := arm (by to_dfin 3) (by to_dfin 0)

noncomputable def Co2_diagram : annotated_graph :=
insert_edge (insert_edge (insert_edge (insert_edge (annotate (annotate (annotate Co2_prediagram (e,f) 6) (a,e) 4) (g,f) 4) (c,d) 4) (c,e) 3) (c,b) 5) (g,b) 4

noncomputable instance Co2_diagram_decidable_rel : decidable_rel Co2_diagram.edge :=
  λ _ _, classical.prop_decidable _

noncomputable def Co2_diagram_group : Group :=
  coxeter_group $ matrix_of_annotated_graph (Co2_diagram)

private def a : Co2_diagram_group := generated_of a
private def b : Co2_diagram_group := generated_of b
private def c : Co2_diagram_group := generated_of c
private def d : Co2_diagram_group := generated_of d
private def e : Co2_diagram_group := generated_of e
private def f : Co2_diagram_group := generated_of f
private def g : Co2_diagram_group := generated_of g

noncomputable def Co2 : Group := Co2_diagram_group/⟪{(c*f)^2 * a⁻¹, (e*f)^3 * b⁻¹, (b*g)^2 * e⁻¹, (a*e*c*d)^4, (c*e*f)^7, (b*a*e*f*g)^3}⟫

end Co2


section Co3
def Co3_prediagram : annotated_graph :=
  annotated_graph_of_graph $ coxeter_edges [1,1,4]

instance Co3_prediagram_decidable_eq : decidable_eq Co3_prediagram.vertex :=
  by apply_instance

noncomputable instance Co3_prediagram_decidable_rel : decidable_rel Co3_prediagram.edge :=
  λ _ _, classical.prop_decidable _

private def a : Co3_prediagram.vertex := torso
private def b : Co3_prediagram.vertex := arm (by to_dfin 1) (by to_dfin 0)
private def c : Co3_prediagram.vertex := arm (by to_dfin 2) (by to_dfin 1)
private def d : Co3_prediagram.vertex := arm (by to_dfin 2) (by to_dfin 2)
private def e : Co3_prediagram.vertex := arm (by to_dfin 2) (by to_dfin 0)
private def f : Co3_prediagram.vertex := arm (by to_dfin 2) (by to_dfin 3)
private def g : Co3_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 0)

noncomputable def Co3_diagram : annotated_graph :=
insert_edge (insert_edge (insert_edge (insert_edge (insert_edge (annotate (Co3_prediagram) (a,e) 4) (g,b) 4) (g,f) 6) (b,c) 5) (f,e) 6) (f,c) 4

noncomputable instance Co3_diagram_decidable_rel : decidable_rel Co3_diagram.edge :=
  λ _ _, classical.prop_decidable _

noncomputable def Co3_diagram_group : Group :=
  coxeter_group $ matrix_of_annotated_graph (Co3_diagram)

private def a : Co3_diagram_group := generated_of a
private def b : Co3_diagram_group := generated_of b
private def c : Co3_diagram_group := generated_of c
private def d : Co3_diagram_group := generated_of d
private def e : Co3_diagram_group := generated_of e
private def f : Co3_diagram_group := generated_of f
private def g : Co3_diagram_group := generated_of g

noncomputable def Co3 : Group := Co3_diagram_group/⟪{(c * f)^2 * a ⁻¹, (e * f)^3 * b⁻¹, (b * g)^2 * d⁻¹, (g*a*e)^3*d⁻¹, (e*a*b)^3, (b*c*e)^5, (a*d*f*g)^3, (c*e*f)^7}⟫

end Co3

end conway_groups
