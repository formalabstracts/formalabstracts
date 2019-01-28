import preliminaries group_theory.sylow group_theory.perm
universe u
open equiv category_theory

/- The alternating groups -/
section
variables {α : Type u} [decidable_eq α] [fintype α]

instance : is_subgroup {g : perm α | g.sign = 1 } := omitted

def alternating_group (n : ℕ) : Group := mk_ob {g : perm (fin n) | g.sign = 1}
end


/-- the "extended" group power, where g^∞ is defined as 1 -/
noncomputable def egpow {α : Type*} [group α] (x : α) (n : enat) : α :=
match n.classical_to_option with
| some n := x ^ n
| none   := 1
end

noncomputable instance {α : Type*} [group α] : has_pow α enat := ⟨egpow⟩

/- Conjugacy Classes -/
variables {α : Type u} [group α]
def is_conjugacy_class (s : set α) : Prop := ∀{{g}} h, g ∈ s → h⁻¹ * g * h ∈ s
-- todo: finite
def conjugacy_class (α : Type*) [group α] : Type* := {s : set α // is_conjugacy_class s}

-- todo:
def conjugacy_class_of_order [fintype α] (N : ℕ) : finset (conjugacy_class α) :=
sorry
