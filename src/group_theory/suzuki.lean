import ..data.dvector .presentation .monster

local notation `⟪`:50 a `⟫`:50 := free_group.of a
local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- From the corresponding entry in the atlas (p. 128) Suz . 2 is a quotient of the group given
  by a certain Coxeter-type presentation   -/

open coxeter_vertices
namespace suzuki
/-- We represent the diagram a--b--c-8-d--e--f--g--h as an annotation of the unlabelled
    coxeter Y-diagram of shape [2,5], so that c is the torso and d belongs to the second arm.-/


noncomputable def abc8defgh_graph : annotated_graph :=
annotate (annotated_graph_of_graph $ coxeter_edges [2,5]) (torso _ ,arm (by to_dfin 1) (by to_dfin 0)) 8

noncomputable instance abc8defgh_decidable_rel : decidable_rel abc8defgh_graph.edge := λ _ _, classical.prop_decidable _

/-- The group generated by the Coxeter-Dynkin diagram a--b--c-8-d--e--f--g--h -/
noncomputable def abc8defgh_group : Group :=
coxeter_group $ matrix_of_annotated_graph abc8defgh_graph

private def a : abc8defgh_group := generated_of $ arm (by to_dfin 0) (by to_dfin 1)
private def b : abc8defgh_group := generated_of $ arm (by to_dfin 0) (by to_dfin 0)
private def c : abc8defgh_group := generated_of $ torso _
private def d : abc8defgh_group := generated_of $ arm (by to_dfin 1) (by to_dfin 0)
private def e : abc8defgh_group := generated_of $ arm (by to_dfin 1) (by to_dfin 1)
private def f : abc8defgh_group := generated_of $ arm (by to_dfin 1) (by to_dfin 2)
private def g : abc8defgh_group := generated_of $ arm (by to_dfin 1) (by to_dfin 3)
private def h : abc8defgh_group := generated_of $ arm (by to_dfin 1) (by to_dfin 4)

/-- Suz.2 is the above group quotiented by additional relations -/
noncomputable def Suz_2 : Group := abc8defgh_group/⟪{(c * d)^4 * a ⁻¹, (b * c * d * e)^8, (b * c * d * c * d * e * f * g * g)^13}⟫

/- As with the monster, since we now have an extension by 2, we can quotient by the center -/

noncomputable def Suz : Group :=
  category_theory.mk_ob $ quotient_group.quotient $ is_subgroup.center $ Suz_2
end suzuki
