import ..basic
       ring_theory.basic
       topology.basic
       category_theory.opposites

open category_theory ideal set

noncomputable theory
universes u v w

def has_coe_ideal {α : Type u} [comm_ring α] : has_coe (ideal α) (set α) := by apply_instance
local attribute [instance] has_coe_ideal

/-- An algebraically closed field is a field where every polynomial with positive degree has a root -/
class algebraically_closed_field (α : Type u) extends discrete_field α :=
(closed : ∀(p : polynomial α), p.degree > 0 → ∃x, p.is_root x)

local attribute [instance, priority 0] classical.prop_decidable
/-- A finitely generated reduced algebra -/
class finitely_generated_reduced_algebra (R : Type u) (A : Type v)
  [comm_ring R] [comm_ring A] extends algebra R A :=
(finitely_generated : ∃(s : finset A), ∀(x : A), ∃(p : mv_polynomial {x // x ∈ s} R),
  p.eval₂ (algebra_map A) subtype.val = x)
(reduced : is_reduced A)

variables (K : Type u) [discrete_field K]
          (R : Type v) [comm_ring R]
          [finitely_generated_reduced_algebra K R]
          {σ : Type w} [decidable_eq σ]

namespace algebraic_geometry

/-- The spectrum `Specm(R)` of a `K`-algebra `R` is the set of homomorphisms from `R` to `K`. -/
@[reducible] def spectrum : Type* := R →ₐ[K] K

variables {R K}
/-- The quotient of R by a maximal ideal is isomorphic to K -/
def quotient_maximal_ideal (I : maximal_ideal R) :
  { f : I.val.quotient ≃ K // is_ring_hom f.to_fun } :=
classical.choice omitted

/-- The spectrum of R is equivalent to the set of maximal ideals on R -/
def spectrum_equiv_maximal_ideal : spectrum K R ≃ maximal_ideal R :=
let f : maximal_ideal R → R → K :=
  λ I, (quotient_maximal_ideal I).val.to_fun ∘ ideal.quotient.mk I.val in
by { haveI h : ∀ I : maximal_ideal R, is_ring_hom (f I) := omitted,
     exact ⟨λ ϕ, ⟨ideal.ker ⇑ϕ, omitted⟩, λ I, ⟨f I, omitted⟩, omitted, omitted⟩ }

variables (K) {R}
/-- `Z(S)` is the set of homomorphisms in `Spec(R)` that vanish on `S`. -/
def Z (S : set R) : set (spectrum K R) := { f | ∀ x ∈ S, f.to_fun x = 0 }

/--`I(X)` consists of all points in `R` that are send to `0` by all `ϕ ∈ X`-/
def I (X : set (spectrum K R)) : set R :=
{ x : R | ∀ϕ : X, ϕ.val x = 0 }

/-- `Z(S)` is equal to `Z` of the radical of the span of `S`. -/
lemma Z_radical_span (S : set R) : Z K ((ideal.span S).radical.carrier) = Z K S :=
omitted

variables (K R)

/-- The Zariski topology is the topology where the closed sets are of the form `Z(S)` for some `S ⊆ R` -/
instance Zariski_topology : topological_space (spectrum K R) :=
⟨set.range (λ S : set R, - Z K S), omitted, omitted, omitted⟩

variables {K R}
/-- A radical ideal gives rise to a closed set in the Zariski topology -/
def closed_set_of_radical_ideal (I : radical_ideal R) :
  subtype (is_closed : set (spectrum K R) → Prop) :=
⟨Z K I.val, mem_range_self I.val⟩

/-- A closed set in the Zariski topology gives rise to a radical ideal -/
def radical_ideal_of_closed_set (X : subtype (is_closed : set (spectrum K R) → Prop)) :
  radical_ideal R :=
⟨⟨ I K X, omitted, omitted, omitted⟩, omitted⟩

/-- Hilbert's Nullstellensatz: there is a correspondence between radical ideals in R and
 closed sets in the spectrum of R. -/
def Nullstellensatz : radical_ideal R ≃ subtype (is_closed : set (spectrum K R) → Prop) :=
⟨closed_set_of_radical_ideal, radical_ideal_of_closed_set, omitted, omitted⟩

variables (K)
/-- In algebraic geometry, the categories of algebra's over K and affine varieties are opposite of each other. In this development we take a shortcut, and *define* affine varieties as the opposite of algebra's over K. -/
@[reducible] def affine_variety : Type* := opposite (Algebra K)

example : category (affine_variety K) := by apply_instance

variables {K R}

/- to do:
* quotient algebras,
* if Z is closed in Spec R, then R / I(Z) is an algebra over K
* The spectrum of this algebra is Z
* affine_variety has a terminal object and binary products
-/

end algebraic_geometry