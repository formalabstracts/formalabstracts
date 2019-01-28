import preliminaries group_theory.sylow group_theory.perm
universe u
open equiv category_theory

section
variables {α : Type u} [decidable_eq α] [fintype α]

instance : is_subgroup {g : perm α | g.sign = 1 } := omitted

def alternating_group (n : ℕ) : Group := mk_ob {g : perm (fin n) | g.sign = 1}
end


variables {α : Type u} [group α]
def is_conjugacy_class (s : set α) : Prop := ∀{{g}} h, g ∈ s → h⁻¹ * g * h ∈ s
-- todo: finite
def conjugacy_class (α : Type*) [group α] : Type* := {s : set α // is_conjugacy_class s}

-- todo:
def conjugacy_class_of_order [fintype α] (N : ℕ) : finset (conjugacy_class α) :=
sorry