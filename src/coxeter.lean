import presentation
noncomputable theory

open set

local notation `⟪`:50 a `⟫`:50 := free_group.of a

/- The dihedral groups -/

/- The dihedral groups are an easy case of the Coxeter groups -/
namespace dihedral_group
def r := ⟪ff⟫
def s := ⟪tt⟫
end dihedral_group
open dihedral_group

/-- The dihedral group of order 2n -/
def dihedral_group (n : ℕ) : Group := ⟪bool | {r^n, s^2, s * r * s * r}⟫

/- Coxeter groups -/

/-- the "extended" group power, where g^∞ is defined as 1 -/
def egpow {α : Type*} [group α] (x : α) (n : enat) : α :=
match n.classical_to_option with
| some n := x ^ n
| none   := 1
end

instance {α : Type*} [group α] : has_pow α enat := ⟨egpow⟩

/-- coxeter group -/
def coxeter_group {n : ℕ} (m : fin n → fin n → enat) : Group := 
⟪fin n | (λ(x : fin n × fin n), (⟪x.1⟫ * ⟪x.2⟫)^m x.1 x.2) '' univ⟫
