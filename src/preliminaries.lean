import data.nat.enat data.set.finite category_theory.isomorphism group_theory.quotient_group
       group_theory.free_group
       
open category_theory

universes u v

axiom omitted {P : Prop} : P

def is_finite (α : Type*) : Prop := nonempty (fintype α) -- set.finite (set.univ : set α)

noncomputable def instantiate_existential {α : Type*} {P : α → Prop} (h : ∃ x, P x) : {x // P x} :=
begin
  haveI : nonempty α := nonempty_of_exists h,
  exact ⟨classical.epsilon P, classical.epsilon_spec h⟩
end

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

noncomputable def roption.classical_to_option {α} (x : roption α) : option α :=
by haveI := classical.dec; exact x.to_option

/- Given N ⊆ G normal, return the canonical surjection G → G/N -/
def canonical_surjection {G : Type*} [group G]  (N : set G) [normal_subgroup N] : G → quotient_group.quotient N:= quotient_group.mk 

instance {G : Type*} [group G]  (N : set G) [normal_subgroup N] : is_group_hom $ canonical_surjection N := omitted

variables {α : Type*} {β : Type*}
def pullback_rel (f : α → β) (r : β → β → Prop) : α → α → Prop := λ x y, r (f x) (f y)
namespace pullback_rel
instance (f : α → β) (r : β → β → Prop) [is_trans β r] : is_trans α (pullback_rel f r) :=
⟨λ x y z h₁ h₂, (trans h₁ h₂ : r (f x) (f z))⟩

protected def is_antisymm (f : α → β) (r : β → β → Prop) (h : function.injective f)
  [is_antisymm β r] : is_antisymm α (pullback_rel f r) :=
⟨λ x y h₁ h₂, h $ antisymm h₁ h₂⟩

instance (f : α → β) (r : β → β → Prop) [is_total β r] : is_total α (pullback_rel f r) :=
⟨λ x y, total_of r (f x) (f y)⟩

instance (f : α → β) (r : β → β → Prop) [decidable_rel r] : decidable_rel (pullback_rel f r) :=
by dsimp [pullback_rel]; apply_instance
end pullback_rel

namespace set
lemma finite_of_subset_finset {s : set α} (t : finset α) (h : s ⊆ ↑t) : s.finite :=
finite_subset (finset.finite_to_set t) h

/-- The cardinality of any subset of a finite type. -/
noncomputable def cardinality [fintype α] (s : set α) : ℕ :=
by haveI := classical.prop_decidable; haveI := (set_fintype s); exact fintype.card s

end set

namespace finset

variables (r : α → α → Prop) [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r] 

lemma sort_length [decidable_eq α] (s : finset α) : (sort r s).length = s.card :=
by rw [←list.to_finset_card_of_nodup (sort_nodup r s), sort_to_finset r s]

end finset

namespace char

protected def to_nat_m65 (c : char) : ℕ := c.val - 65

end char