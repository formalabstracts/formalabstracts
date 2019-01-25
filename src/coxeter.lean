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
-- We could require that m i i = 1 for all i : α
def coxeter_group {α : Type*} (m : α → α → enat) : Group := 
⟪α | (λ(x : α × α), (⟪x.1⟫ * ⟪x.2⟫)^m x.1 x.2) '' univ⟫

def matrix_of_graph {α : Type*} [decidable_eq α] (E : α → α → Prop) [decidable_rel E] (x y : α) :
  enat :=
if x = y then 1 else if E x y then 3 else 2
