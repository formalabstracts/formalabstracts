import order.filter data.set meta_data data.list data.vector
       topology.real topology.continuity topology.metric_space
       algebra.module data.finset.basic  -- .metric
       .complex

noncomputable theory

open set filter classical ring

local attribute [instance] prop_decidable

universes u v

section
variables (α : Type u) [field α]

-- valuation on a field.
-- see Berkovich, page 2, http://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf
class valuation extends metric_space α :=
(val : α → ℝ)
-- (nonneg : ∀ x, val x ≥ 0)
(multiplicative : ∀ x y, val (x * y) = val x * val y)
-- (triangle: ∀ x y, val (x + y) ≤ val x + val y)
(valdist : ∀ x y, dist x y = val (x - y))

end

section

variables (α : Type u) 

#print distrib
#print monoid

-- set_option old_structure_cmd true -- ring.lean
class ring_ (α : Type u) extends add_comm_group α, monoid α, distrib α
class rng (α : Type u) extends add_comm_group α, semigroup α, distrib α


class ideal :=
(carrier : set α)
(closure_add : ∀ x y, x ∈ carrier ∧ y ∈ carrier → x - y ∈ carrier)
(closure_mul : ∀ a x, x ∈ carrier → a*x ∈ carrier ∧ x* a ∈ carrier)

#print fields ring
#check ring.one


end





variables (α : Type u) [field α] [valuation α] 

class subring

axiom ring_of_integers_exists : 
(∃! h, h : ring (sub
def ring_of_integers := 
