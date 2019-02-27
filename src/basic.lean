/- This file contains various definitions and lemmas which don't fit anywhere else, or when there
  is not enough material to make its own file -/

import data.pfun data.set.finite data.nat.enat topology.basic
import tactic.fattribute
universes u v

variables {α : Type*} {β : Type*}

axiom omitted {P : Prop} : P

notation `ℕ∞` := enat

def is_finite (α : Type*) : Prop := nonempty (fintype α) -- set.finite (set.univ : set α)

noncomputable def roption.classical_to_option {α} (x : roption α) : option α :=
by haveI := classical.dec; exact x.to_option

namespace vector
  noncomputable def vector_one_equiv : vector α 1 ≃ α :=
  classical.choice omitted
end vector

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

/-- the pullback of a relation along a function -/
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

namespace topological_space

variables (α) [topological_space α]
@[reducible] def closed_set : Type* := subtype (is_closed : set α → Prop)

end topological_space
