import ..basic
       ring_theory.ideal_operations ring_theory.algebra
       topology.basic
       linear_algebra.tensor_product
  category_theory.concrete_category

universes u v

/-- An algebraically closed field is a field where every polynomial with positive degree has a root -/
class algebraically_closed_field (α : Type u) extends discrete_field α :=
(closed : ∀(p : polynomial α), p.degree > 0 → ∃x, p.is_root x)

def is_nilpotent {α : Type u} [comm_semiring α] (x : α) : Prop := ∃ n : ℕ, x^n = 0
def is_radical {α : Type u} [comm_ring α] (I : ideal α) : Prop := I = I.radical

local attribute [instance, priority 0] classical.prop_decidable
/-- A finitely generated algebra without nilpotents -/
class finitely_generated_algebra_without_nilpotents (R : Type u) (A : Type v)
  [comm_ring R] [comm_ring A] extends algebra R A :=
(finitely_generated : ∃(s : finset A), ∀(x : A), ∃(p : mv_polynomial {x // x ∈ s} R),
  p.eval₂ (algebra_map A) subtype.val = x)
(no_nilpotents : ∀(x : A), is_nilpotent x → x = 0)

variables (K : Type u) [algebraically_closed_field K] (R : Type v) [comm_ring R]
          [finitely_generated_algebra_without_nilpotents K R]

/-- The spectrum `Spec(R)` of a `K`-algebra `R` is the set of homomorphisms from `R` to `K`. -/
def spectrum : Type* := R →ₐ[K] K

variables {R}
/-- `Z(S)` is the set of homomorphisms in `Spec(R)` that vanish on `S`. -/
def Z (S : set R) : set (spectrum K R) := { f | ∀ x ∈ S, f.to_fun x = 0 }

/-- `Z(S)` is equal to `Z` of the radical of the span of `S`. -/
lemma Z_radical_span (S : set R) : Z K ((ideal.span S).radical.carrier) = Z K S :=
omitted

variables (K R)

/-- The Zariski topology is the topology where the closed sets are of the form `Z(S)` for some `S ⊆ R` -/
instance Zariski_topology : topological_space (spectrum K R) :=
⟨{ Y | ∃S : set R, Y = -Z K S }, omitted, omitted, omitted⟩

/- Can we easily get the category of algebra's over a field K? -/
-- /-- The type of groups. -/
-- @[reducible] def Alg (α : Type u) [comm_ring α] : Type* :=
-- category_theory.bundled (λ(A : Type v), Σ[h : ring A], by exactI algebra α A)

-- /-- Group + group homomorphisms form a concrete category -/
-- instance concrete_is_group_hom : category_theory.concrete_category alg_hom :=
-- ⟨by introsI α ia; apply_instance, by introsI α β γ ia ib ic f g hf hg; apply_instance⟩


