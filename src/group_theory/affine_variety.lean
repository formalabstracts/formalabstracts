import ring_theory.basic
       ..category_theory.group_object
       ..category_theory.limits2
       tactic.omitted
       category_theory.limits.opposites

open category_theory ideal set topological_space

noncomputable theory
universes u v w

def has_coe_ideal {α : Type u} [comm_ring α] : has_coe (ideal α) (set α) := by apply_instance
local attribute [instance] has_coe_ideal

/-- An algebraically closed field is a field where every polynomial with positive degree has a root -/
class algebraically_closed_field (α : Type u) extends discrete_field α :=
(closed : is_algebraically_closed α)

local attribute [instance, priority 0] classical.prop_decidable
/-- A finitely generated reduced algebra -/
class finitely_generated_reduced_algebra (R : Type u) (A : Type v)
  [comm_ring R] [comm_ring A] extends algebra R A :=
(finitely_generated : is_finitely_generated R A)
(reduced : is_reduced A)

variables (K : Type u) [discrete_field K]
          (R : Type v) [comm_ring R] (S : Type w) [comm_ring S]
          [finitely_generated_reduced_algebra K R] [finitely_generated_reduced_algebra K S]
          {σ : Type w} [decidable_eq σ]

open finitely_generated_reduced_algebra
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
def closed_set_of_radical_ideal (I : radical_ideal R) : closed_set (spectrum K R) :=
⟨Z K I.val, mem_range_self I.val⟩

/-- A closed set in the Zariski topology gives rise to a radical ideal -/
def radical_ideal_of_closed_set (X : closed_set (spectrum K R)) :
  radical_ideal R :=
⟨⟨ I K X, omitted, omitted, omitted⟩, omitted⟩

/-- Hilbert's Nullstellensatz: there is a correspondence between radical ideals in R and
 closed sets in the spectrum of R. -/
def Nullstellensatz : radical_ideal R ≃ closed_set (spectrum K R) :=
⟨closed_set_of_radical_ideal, radical_ideal_of_closed_set, omitted, omitted⟩

instance base.finitely_generated_reduced_algebra :
  finitely_generated_reduced_algebra K K :=
{ finitely_generated := is_finitely_generated_base K,
  reduced := is_reduced_integral_domain,
  .._inst_1 }

instance quotient.finitely_generated_reduced_algebra (I : radical_ideal R) :
  finitely_generated_reduced_algebra K I.1.quotient :=
{ finitely_generated := is_finitely_generated_quotient (finitely_generated K R) I.1,
  reduced := is_reduced_quotient I.2,
  ..quotient.algebra I.1 }

variables (R S)
instance tensor.finitely_generated_reduced_algebra :
  finitely_generated_reduced_algebra K (R ⊗[K] S) :=
{ finitely_generated := is_finitely_generated_tensor
  (finitely_generated K R) (finitely_generated K S),
  reduced := is_reduced_tensor (reduced K R) (reduced K S),
  ..tensor_product.algebra }

variables {R S}

/-- The type of finitely generated reduced algebras over a fixed commutative ring. -/
structure FRAlgebra (R : Type u) [comm_ring R] : Type (u+1) :=
  (β : Type u)
  [ring : comm_ring β]
  [algebra : finitely_generated_reduced_algebra R β]

attribute [instance] FRAlgebra.ring FRAlgebra.algebra
instance (R : Type v) [comm_ring R] : has_coe_to_sort (FRAlgebra R) :=
{ S := Type v, coe := FRAlgebra.β }

open category_theory
/-- The category of finitely generated reduced algebras over a fixed commutative ring. -/
instance FRAlgebra.category (R : Type u) [comm_ring R] : large_category (FRAlgebra R) :=
{ hom   := λ a b, a.β →ₐ[R] b.β,
  id    := λ a, alg_hom.id R a,
  comp  := λ a b c f g, alg_hom.comp g f }

def FRAlgebra.quotient (R : FRAlgebra K) (Z : closed_set (spectrum K R)) : FRAlgebra K :=
⟨K, (radical_ideal_of_closed_set Z).1.quotient⟩

def FRAlgebra_tensor (R S : FRAlgebra K) : FRAlgebra K :=
{ β := R ⊗[K] S,
  ring := _,
  algebra := tensor.finitely_generated_reduced_algebra R S }

variables (K)
def FRAlgebra_self : FRAlgebra K := ⟨K, K⟩

lemma FRAlgebra_self_hom (R : FRAlgebra K) : (R ⟶ FRAlgebra_self K) = (R →ₐ[K] K) := by refl
lemma FRAlgebra_self_hom' (R : FRAlgebra K) : (by exact R ⟶ FRAlgebra_self K) = spectrum K R := rfl

open tensor_product
lemma FRAlgebra.has_binary_coproducts : limits.has_binary_coproducts (FRAlgebra K) :=
begin
  constructor, intros F, resetI,
  use FRAlgebra_tensor
    (F.obj category_theory.limits.two.left) (F.obj category_theory.limits.two.right),
  { refine ⟨_, omitted⟩, intro x, cases x, apply tensor_inl, apply tensor_inr },
  refine ⟨_, omitted, omitted⟩, intro s,
  refine tensor_lift (s.ι.app limits.two.left) (s.ι.app limits.two.right)
end

lemma FRAlgebra.has_initial_object : limits.has_initial_object (FRAlgebra K) :=
begin
  constructor, intros F, resetI,
  use FRAlgebra_self K,
  { refine ⟨_, omitted⟩, rintro ⟨⟩ },
  refine ⟨_, omitted, omitted⟩, intro s, dsimp,
  exact sorry --todo
end

/-- In algebraic geometry, the categories of algebra's over K and affine varieties are opposite of each other. In this development we take a shortcut, and *define* affine varieties as the opposite of algebra's over K. -/
@[reducible] def affine_variety : Type* := opposite (FRAlgebra K)

@[instance] def affine_variety.category : large_category (affine_variety K) := by apply_instance

def affine_variety.subobject (R : affine_variety K) (Z : closed_set (spectrum K ↥(unop R))) :
  FRAlgebra K :=
FRAlgebra.quotient (unop R) Z

@[instance] lemma affine_variety.has_binary_products :
  limits.has_binary_products (affine_variety K) :=
by { haveI : limits.has_colimits_of_shape.{u} (discrete limits.two) (FRAlgebra K) :=
     FRAlgebra.has_binary_coproducts K, exact limits.has_products_opposite _ }

@[instance] lemma affine_variety.has_terminal_object :
  limits.has_terminal_object (affine_variety K) :=
by { haveI : limits.has_colimits_of_shape.{u} (discrete pempty) (FRAlgebra K) :=
     FRAlgebra.has_initial_object K, exact limits.has_products_opposite _ }

-- @[instance] lemma affine_variety.complete : limits.has_limits.{u} (affine_variety K) := _

/- The underlying type of an affine variety G = Rᵒᵖ is Spec(R), equivalently the global points
   of G in the category of affine varieties. It is easy to show that the global points functor
   in a category with finite limits is left-exact. -/
def algebraic_variety.type : (affine_variety K) ⥤ Type* :=
{ obj := λ X, (unop X) ⟶ (FRAlgebra_self K),
  map := λ X Y f ϕ, f.unop ≫ ϕ,
  map_id' := by tidy,
  map_comp' := by tidy}

variables {K R}

/- to do:
* quotient algebras,
* if Z is closed in Spec R, then R / I(Z) is an algebra over K
* The spectrum of this algebra is Z
* affine_variety has a terminal object and binary products
-/

end algebraic_geometry

section algebraic_group
open algebraic_geometry
variables (K) [discrete_field K]
/- For our purposes, an algebraic group is a group object in the category of affine varieties -/
include K
def algebraic_group : Type* := group_object (affine_variety K)

/- to do:
* group instance on underlying type of algebraic group
* statement that algebraic_variety.type preserves finite products (is just left-exact)
-/

end algebraic_group
