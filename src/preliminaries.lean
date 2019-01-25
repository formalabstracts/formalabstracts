import data.set.finite category_theory.isomorphism

open category_theory

universe u

axiom omitted {P : Prop} : P

def is_finite (α : Type*) : Prop := nonempty (fintype α) -- set.finite (set.univ : set α)


/-- The category of groups. -/
@[reducible] def Group : Type (u+1) := bundled group

namespace Group
noncomputable def order (G : Group) (h : is_finite G) : ℕ :=
@fintype.card G (classical.choice h)

instance (G : Group) : group G := G.str
end Group

instance concrete_is_group_hom : concrete_category @is_group_hom :=
⟨by introsI α ia; apply_instance, by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

variables (G H : Group.{u})
#check G ⟶ H
#check G ≅ H

