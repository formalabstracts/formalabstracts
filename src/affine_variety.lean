import ring_theory.ideal_operations data.polynomial ring_theory.algebra

universes u v

class algebraically_closed_field (α : Type u) extends discrete_field α :=
(closed : ∀(p : polynomial α), p.degree > 0 → ∃x, p.is_root x)


