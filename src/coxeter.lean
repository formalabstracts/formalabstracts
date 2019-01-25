import presentation

open group_language presentation

/- The dihedral groups -/

local notation `⟨`:50 a `⟩`:50 := free_group.of a

/- The dihedral groups are an easy case of the Coxeter groups -/

inductive dihedral_group_generators
| r : dihedral_group_generators
| s : dihedral_group_generators

open dihedral_group_generators

def G := dihedral_group_generators

def dihedral_group (n : ℕ) : Group := ⟨G | {⟨r⟩^n, ⟨s⟩^2, ⟨s⟩ * ⟨r⟩ * ⟨s⟩ * ⟨r⟩}⟩

-- TODO coxeter groups
