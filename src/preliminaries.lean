import data.set.finite category_theory.isomorphism

open category_theory

universes u v

axiom omitted {P : Prop} : P

def is_finite (α : Type*) : Prop := nonempty (fintype α) -- set.finite (set.univ : set α)

/-- The type of groups. -/
@[reducible] def Group : Type (u+1) := bundled group

namespace Group
/-- The order of a finite group is defined as its cardinality  -/
noncomputable def order (G : Group) (h : is_finite G) : ℕ :=
@fintype.card G (classical.choice h)

instance (G : Group) : group G := G.str
end Group

/-- Group + group homomorphisms form a concrete category -/
instance concrete_is_group_hom : concrete_category @is_group_hom :=
⟨by introsI α ia; apply_instance, by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

/-- Transferring the structure of a group along an equivalence of types -/
def group.equiv {α β} (e : α ≃ β) [group α] : group β :=
begin
  refine {mul := λ x y, e (e.symm x * e.symm y), one := e 1, inv := λ x, e (e.symm x)⁻¹, ..},
  all_goals {exact omitted}
end

/-- The group structure on the universe lift of a type -/
instance ulift.group {α} [group α] : group (ulift α) :=
group.equiv (by tidy : ulift α ≃ α).symm

/-- The universe lift of a group -/
def glift (G : Group.{u}) : Group.{max u v} :=
⟨ulift G, by apply_instance⟩

/-- This is the notion of isomorphic groups which might live in arbitrary universe levels -/
def isomorphic (G : Group.{u}) (H : Group.{v}) : Prop :=
nonempty (glift.{u v} G ≅ glift.{v u} H)
