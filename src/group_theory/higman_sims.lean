import ..data.dvector .presentation .monster

local notation `⟪`:50 a `⟫`:50 := free_group.of a
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- From the corresponding entry in the atlas (p. 123) the Higman-Sims sporadic group is given by a generalized Coxeter-type presentation modulo additional relations -/

open coxeter_vertices
namespace higman_sims

/- The graph is question is

a--b-4-c--d--e
 ↘ ↓     ↙5
4  f

which we'll write as the annotated_graph of a Coxeter Y-diagram with the diagonal edges inserted
-/

def higman_sims_prediagram : annotated_graph := -- above diagram without diagonals or annotations
  annotated_graph_of_graph $ coxeter_edges [1,3,1]

instance higman_sims_prediagram_decidable_eq : decidable_eq higman_sims_prediagram.vertex :=
  by apply_instance

noncomputable instance higman_sims_prediagram_decidable_rel : decidable_rel higman_sims_prediagram.edge :=
  λ _ _, classical.prop_decidable _

private def a : higman_sims_prediagram.vertex := arm (by to_dfin 0) (by to_dfin 0)
private def b : higman_sims_prediagram.vertex:= torso
private def c : higman_sims_prediagram.vertex := arm (by to_dfin 1) (by to_dfin 0)
private def d : higman_sims_prediagram.vertex:= arm (by to_dfin 1) (by to_dfin 1)
private def e : higman_sims_prediagram.vertex := arm (by to_dfin 1) (by to_dfin 2)
private def f : higman_sims_prediagram.vertex:= arm (by to_dfin 2) (by to_dfin 0)

noncomputable instance higman_sims_decidable_rel : decidable_rel ((insert_edge (annotate higman_sims_prediagram (b, c) 4) (a, f) 4).edge) := by apply_instance

noncomputable def higman_sims_diagram : annotated_graph :=
insert_edge (insert_edge (annotate higman_sims_prediagram (b,c) 4) (a,f) 4) (d,f) 5

noncomputable instance higman_sims_diagram_decidable_rel : decidable_rel higman_sims_diagram.edge := λ _ _, classical.prop_decidable _

noncomputable def higman_sims_diagram_group : Group :=
  coxeter_group $ matrix_of_annotated_graph (higman_sims_diagram)

private def a : higman_sims_diagram_group := generated_of a
private def b : higman_sims_diagram_group:= generated_of b
private def c : higman_sims_diagram_group := generated_of c
private def d : higman_sims_diagram_group:= generated_of d
private def e : higman_sims_diagram_group := generated_of e
private def f : higman_sims_diagram_group:= generated_of f

noncomputable def HS : Group := higman_sims_diagram_group/⟪{(f * a)^2 * e⁻¹, (c * b * f)^3, (f * d * c)^5, (b * c * d * e)^4}⟫

end higman_sims
