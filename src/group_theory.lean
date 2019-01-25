import preliminaries group_theory.sylow group_theory.perm
universe u
open equiv category_theory

variables {α : Type u} [decidable_eq α] [fintype α]

instance : is_subgroup {g : perm α | g.sign = 1 } := omitted

def alternating_group (n : ℕ) : Group := mk_ob {g : perm (fin n) | g.sign = 1}

