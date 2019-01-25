import presentation

open group_language presentation

/- The dihedral groups -/

local notation a `̂ `:70 k:70 := term.pow (term_mk a) k

local notation a `×'`:75 b:75 := term.mul (term_mk a) (b)

local notation a`⁻¹`:65 := term.inv (term_mk a)

local notation t₁ `≃`:60 t₂ := relation.eq t₁ t₂

notation a `×'`:75 b:75 := term.mul (term_mk a) (term_mk b)

/- The dihedral groups are an easy case of the Coxeter groups -/

inductive dihedral_group_generators
| r : dihedral_group_generators
| s : dihedral_group_generators

open dihedral_group_generators

def G := dihedral_group_generators

def dihedral_group (n) : Group := ⟨G | [r ̂ n ≃ 1, s ̂ 2 ≃ 1, s ×' (r ×' s) ≃ r⁻¹]⟩

-- TODO coxeter groups
