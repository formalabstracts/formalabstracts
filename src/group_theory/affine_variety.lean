import ..basic
       ring_theory.ideal_operations ring_theory.algebra
       topology.basic
       linear_algebra.tensor_product
  category_theory.concrete_category

noncomputable theory

universes u v w

def has_coe_ideal {α : Type u} [comm_ring α] : has_coe (ideal α) (set α) := by apply_instance
local attribute [instance] has_coe_ideal

/-- An algebraically closed field is a field where every polynomial with positive degree has a root -/
class algebraically_closed_field (α : Type u) extends discrete_field α :=
(closed : ∀(p : polynomial α), p.degree > 0 → ∃x, p.is_root x)

def is_nilpotent {α : Type u} [comm_semiring α] (x : α) : Prop := ∃ n : ℕ, x^n = 0
def is_radical {α : Type u} [comm_ring α] (I : ideal α) : Prop := I = I.radical
def is_reduced (α : Type u) [comm_semiring α] : Prop := ∀(x : α), is_nilpotent x → x = 0

section
local attribute [instance, priority 0] classical.prop_decidable
/-- A finitely generated reduced algebra -/
class finitely_generated_reduced_algebra (R : Type u) (A : Type v)
  [comm_ring R] [comm_ring A] extends algebra R A :=
(finitely_generated : ∃(s : finset A), ∀(x : A), ∃(p : mv_polynomial {x // x ∈ s} R),
  p.eval₂ (algebra_map A) subtype.val = x)
(reduced : is_reduced A)
end

variables (K : Type u) [discrete_field K]
          (R : Type v) [comm_ring R]
          [finitely_generated_reduced_algebra K R]
          {σ : Type w} [decidable_eq σ]

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

variables {K R}


/- The geometric side -/

/-- The zero locus `Z(S)` of a set of polynomials S is the set of points which are sent to 0 -/
def zero_locus (s : set (mv_polynomial σ K)) : set (σ → K) :=
{ x | ∀{f : mv_polynomial σ K}, f ∈ s → f.eval x = 0 }

lemma zero_locus_span (s : set (mv_polynomial σ K)) : zero_locus ↑(ideal.span s) = zero_locus s :=
omitted

/-- A set is algebraic if it is the zero locus of a set of polynomials -/
def is_algebraic (s : set (σ → K)) : Prop := s ∈ set.range (zero_locus : _ → set (σ → K))

-- def algebraic_variety : Type := sorry

-- def affine_variety : Type := sorry

