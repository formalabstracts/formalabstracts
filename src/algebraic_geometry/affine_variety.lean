/- In this file we define affine varieties and affine groups over a discrete field `K`.
  We take a shortcut in the definition, by defining affine varieties as the opposite
  category of finitely generated reduced algebras. We define affine groups and basic
  group theory for affine groups: closed subgroups, kernels, normal subgroups, solvable groups, Borel subgroups, centralizers. -/
import ring_theory.basic
       ..category_theory.group_object
       ..category_theory.limits2
       tactic.omitted
       category_theory.limits.opposites
       topology.opens

open category_theory ideal set topological_space

noncomputable theory
universes u v w

-- we set some priorities of instances very low, because they cause problems in this file
local attribute [instance, priority 1] limits.category_theory.limits.has_limit
  limits.category_theory.limits.has_colimit limits.category_theory.limits.has_colimits
  limits.category_theory.limits.has_limits limits.category_theory.limits.has_limits_of_shape
  limits.category_theory.limits.has_colimits_of_shape

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

open finitely_generated_reduced_algebra category_theory tensor_product
namespace algebraic_geometry

/-- The spectrum `Specm(R)` of a `K`-algebra `R` is the set of homomorphisms from `R` to `K`.
  This corresponds to maximal ideals in `R`. -/
@[reducible] def spectrum : Type* := R →ₐ[K] K

variables {R K}
/-- The quotient of R by a maximal ideal is isomorphic to K -/
def quotient_maximal_ideal (I : maximal_ideal R) :
  { f : I.val.quotient ≃ K // is_ring_hom f.to_fun } :=
classical.choice omitted -- TODO: fix non-canoncial choice

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
def closeds_of_radical_ideal (I : radical_ideal R) : closeds (spectrum K R) :=
⟨Z K I.val, mem_range_self I.val⟩

/-- A closed set in the Zariski topology gives rise to a radical ideal -/
def radical_ideal_of_closeds (X : closeds (spectrum K R)) : radical_ideal R :=
⟨⟨ I K X.val, omitted, omitted, omitted⟩, omitted⟩

/-- Hilbert's Nullstellensatz: there is a correspondence between radical ideals in R and
 closed sets in the spectrum of R. -/
def Nullstellensatz : radical_ideal R ≃ closeds (spectrum K R) :=
⟨closeds_of_radical_ideal, radical_ideal_of_closeds, omitted, omitted⟩

instance base.finitely_generated_reduced_algebra :
  finitely_generated_reduced_algebra K K :=
{ finitely_generated := is_finitely_generated_base K,
  reduced := is_reduced_integral_domain,
  .._inst_1 }

instance quotient.finitely_generated_reduced_algebra (I : radical_ideal R) :
  finitely_generated_reduced_algebra K I.val.quotient :=
{ finitely_generated := is_finitely_generated_quotient (finitely_generated K R) I.val,
  reduced := is_reduced_quotient I.2,
  ..quotient.algebra I.val }

variables (R S)
instance tensor.finitely_generated_reduced_algebra :
  finitely_generated_reduced_algebra K (R ⊗[K] S) :=
{ finitely_generated := is_finitely_generated_tensor
  (finitely_generated K R) (finitely_generated K S),
  reduced := is_reduced_tensor (reduced K R) (reduced K S),
  ..tensor_product.algebra }

/-- For a closed subset `Z` the quotient `K[X]/I(Z)` is an algebra over `K` -/
example (Z : closeds (spectrum K R)) : algebra K (radical_ideal_of_closeds Z).val.quotient :=
infer_instance

/-- The spectrum of `K[X]/I(Z)` is Z for a closed subset `Z` -/
def spectrum_quotient (Z : closeds (spectrum K R)) :
  spectrum K (radical_ideal_of_closeds Z).val.quotient ≃ₜ Z.val :=
{ to_fun := λ x, ⟨x.comp $ algebra.quotient.mk _, omitted⟩,
  inv_fun := λ y, algebra.quotient.lift y omitted,
  left_inv := omitted,
  right_inv := omitted,
  continuous_to_fun := omitted,
  continuous_inv_fun := omitted }

variables {R S}

/-- The type of finitely generated reduced algebras over a fixed commutative ring. -/
structure FRAlgebra (R : Type u) [comm_ring R] : Type (u+1) :=
  (β : Type u)
  [ring : comm_ring β]
  [algebra : finitely_generated_reduced_algebra R β]

attribute [instance, priority 1100] FRAlgebra.ring FRAlgebra.algebra
instance (R : Type v) [comm_ring R] : has_coe_to_sort (FRAlgebra R) :=
{ S := Type v, coe := FRAlgebra.β }

/-- The category of finitely generated reduced (f.g.r.) algebras over a fixed commutative ring. -/
instance FRAlgebra.category (R : Type u) [comm_ring R] : large_category (FRAlgebra R) :=
{ hom   := λ a b, a.β →ₐ[R] b.β,
  id    := λ a, alg_hom.id R a,
  comp  := λ a b c f g, alg_hom.comp g f }

/-- Quotients in the category of f.g.r. algebras -/
def FRAlgebra.quotient (R : FRAlgebra K) (Z : closeds (spectrum K R)) : FRAlgebra K :=
⟨K, (radical_ideal_of_closeds Z).val.quotient⟩

/-- The quotient map in the category of f.g.r. algebras -/
def FRAlgebra.quotient_map (R : FRAlgebra K) (Z : closeds (spectrum K R)) :
  R ⟶ R.quotient Z :=
algebra.quotient.mk _

/-- The tensor product of two finitely generated reduced algebras over `K` -/
def FRAlgebra_tensor (R S : FRAlgebra K) : FRAlgebra K :=
{ β := R ⊗[K] S,
  ring := _,
  algebra := tensor.finitely_generated_reduced_algebra R S }

variables (K)
section
local attribute [instance, priority 1500] algebra.mv_polynomial algebra.polynomial
/-- Polynomials over `K` as an f.g.r. algebra over `K` -/
def FRAlgebra_polynomial : FRAlgebra K :=
{ β := polynomial K,
  algebra := { finitely_generated := omitted,
               reduced := omitted } }

/-- Multivariate polynomials over `K` as an f.g.r. algebra over `K` -/
def FRAlgebra_mv_polynomial (K : Type (max u v)) [discrete_field K] (σ : Type v)
  [decidable_eq σ] : FRAlgebra K :=
{ β := mv_polynomial σ K,
  algebra := { finitely_generated := omitted,
               reduced := omitted } }
end

/-- `K` forms a finitely generated reduced algebras over `K` -/
def FRAlgebra_id : FRAlgebra K := ⟨K, K⟩

example (R : FRAlgebra K) : (R ⟶ FRAlgebra_id K) = (R.β →ₐ[K] K) := by refl
example (R : FRAlgebra K) : (R ⟶ FRAlgebra_id K) = spectrum K R.β := rfl

/-- The category of finitely generated reduced algebras over `K` has binary coproducts -/
def FRAlgebra.has_binary_coproducts : limits.has_binary_coproducts (FRAlgebra K) :=
begin
  fapply limits.has_binary_coproducts.mk FRAlgebra_tensor,
  exact λ X Y, tensor_inl,
  exact λ X Y, tensor_inr,
  exact λ X Y Z, tensor_lift,
  omit_proofs
end

/-- The category of finitely generated reduced algebras over `K` has an initial object -/
def FRAlgebra.has_initial_object : limits.has_initial_object (FRAlgebra K) :=
begin
  fapply limits.has_initial_object.mk (FRAlgebra_id K),
  intro X, exact algebra.of_id K X,
  omitted
end

/-- In algebraic geometry, the categories of algebra's over `K` and affine varieties are opposite of each other. In this development we take a shortcut, and *define* affine varieties as the opposite of algebra's over K. -/
@[reducible] def affine_variety : Type* := opposite (FRAlgebra K)

example : large_category (affine_variety K) := by apply_instance

/-- The category of affine varieties has binary products -/
@[instance, priority 1200] def affine_variety.has_binary_products :
  limits.has_binary_products (affine_variety K) :=
by { haveI : limits.has_colimits_of_shape.{u} (discrete limits.two) (FRAlgebra K) :=
     FRAlgebra.has_binary_coproducts K, exact limits.has_products_opposite _ }

/-- The category of affine varieties has a terminal object -/
@[instance, priority 1200] def affine_variety.has_terminal_object :
  limits.has_terminal_object (affine_variety K) :=
by { haveI : limits.has_colimits_of_shape.{u} (discrete pempty) (FRAlgebra K) :=
     FRAlgebra.has_initial_object K, exact limits.has_products_opposite _ }

/-- The underlying type of an affine variety G = Rᵒᵖ is Spec(R), equivalently the global points
   of G in the category of affine varieties. -/
def affine_variety.type_functor : affine_variety K ⥤ Type u :=
yoneda.obj (FRAlgebra_id K)

/- to do: affine_variety.type_functor preserves finite products (is just left-exact) -/
variables {K R}

/-- The object part of the functor `affine_variety.type_functor` -/
def affine_variety.type (X : affine_variety K) : Type u :=
(affine_variety.type_functor K).obj X

/-- The type of `X` is the spectrum of `X` viewed as an object in the opposite category -/
lemma affine_variety.type_eq (X : affine_variety K) :
  affine_variety.type X = spectrum K (unop X).β := rfl

/-- We tell Lean that the Zariski topology gives a topology on the type of an affine variety -/
instance (X : affine_variety K) : topological_space X.type :=
algebraic_geometry.Zariski_topology _ _

/-- A subobject of an affine variety given by a closed set on its type -/
def affine_variety.subobject (X : affine_variety K) (Z : closeds X.type) : affine_variety K :=
op ((unop X).quotient Z)

/-- A subobject of an affine variety given by a closed set on its type -/
def affine_variety.incl (X : affine_variety K) (Z : closeds X.type) :
  X.subobject Z ⟶ X :=
(FRAlgebra.quotient_map _ _).op

/-- A subobject of an affine variety given by a closed set on its type -/
def incl_of_subset {X : affine_variety K} {Z₁ Z₂ : closeds X.type} (h : Z₁.1 ⊆ Z₂.1) :
  X.subobject Z₁ ⟶ X.subobject Z₂ :=
has_hom.hom.op (algebra.quotient.lift (algebra.quotient.mk _) omitted)

/-- Inclusion of a set on the type of a subobject into the sets on type type of `X` -/
def set_sub_incl {X : affine_variety K} {Z : closeds X.type} :
  set (X.subobject Z).type → set X.type :=
image $ (affine_variety.type_functor K).map $ X.incl Z


variable (K)
/-- An affine group is a group object in the category of affine varieties -/
abbreviation affine_group : Type* := group_object (affine_variety K)

example : category (affine_group K) := by apply_instance

end algebraic_geometry

open algebraic_geometry
variables variables {K} {G G' G₁ G₂ G₃ H : affine_group K}

/-- A morphism between affine groups induces a map between the types -/
def group_hom.type (f : G ⟶ G') : G.obj.type → G'.obj.type :=
(affine_variety.type_functor K).map f.map

namespace algebraic_geometry

-- Given an algebraic group, we get a group structure on its type
section
set_option class.instance_max_depth 80
/-- The multiplication on the type of an affine group -/
def group_type_mul (f g : G.obj.type) : G.obj.type := (tensor_lift f g).comp G.mul.unop
end

/-- The inversion on the type of an affine group -/
def group_type_inv (f : G.obj.type) : G.obj.type := f.comp G.inv.unop

/-- The unit in the type of an affine group -/
def group_type_one : G.obj.type := G.one.unop

/-- Given an algebraic group, we get a group structure on its type -/
instance group_type (G : affine_group K) : group G.obj.type :=
{ mul := group_type_mul,
  mul_assoc := omitted,
  one := group_type_one,
  one_mul := omitted,
  mul_one := omitted,
  inv := group_type_inv,
  mul_left_inv := omitted }

/-- A morphism between affine groups induces a group homomorphism between the types -/
instance (f : G ⟶ G') : is_group_hom f.type := omitted

/-- A closed subgroup of G is a subset of its type that is closed and a subgroup -/
class is_closed_subgroup (s : set G.obj.type) extends is_subgroup s : Prop :=
(closed : is_closed s)

/-- The type of `G` is a closed subgroup of itself -/
instance is_closed_subgroup_univ (G : affine_group K) :
  is_closed_subgroup (univ : set G.obj.type) :=
omitted

/-- A closed subgroup gives a closed set (by forgetting that it is a subgroup) -/
def to_closeds (s : set G.obj.type) [is_closed_subgroup s] : closeds G.obj.type :=
⟨s, is_closed_subgroup.closed s⟩

/-- The (opposite of the) multiplication on a subgroup -/
def sub_mul_op (s : set G.obj.type) [is_closed_subgroup s] : (unop G.obj).quotient (to_closeds s) ⟶
  FRAlgebra_tensor ((unop G.obj).quotient (to_closeds s)) ((unop G.obj).quotient (to_closeds s)) :=
algebra.quotient.lift
  begin
    refine alg_hom.comp _ G.mul.unop,
    exact tensor_functor (algebra.quotient.mk _) (algebra.quotient.mk _)
  end
 omitted

/-- From a closed subgroup we can construct an affine group -/
def sub (s : set G.obj.type) [is_closed_subgroup s] : affine_group K :=
{ obj := G.obj.subobject (to_closeds s),
  mul := (sub_mul_op s).op,
  mul_assoc := omitted,
  one := (show (unop G.obj).quotient (to_closeds s) ⟶ FRAlgebra_id K,
          from algebra.quotient.lift G.one.unop omitted).op,
  one_mul := omitted,
  mul_one := omitted,
  inv := (show (unop G.obj).quotient (to_closeds s) ⟶ (unop G.obj).quotient (to_closeds s),
          from algebra.quotient.functor G.inv.unop omitted).op,
  mul_left_inv := omitted }

def affine_group.incl (G : affine_group K) (s : set G.obj.type) [is_closed_subgroup s] :
  sub s ⟶ G :=
by exact ⟨affine_variety.incl _ _, omitted⟩

instance set_sub_incl.is_closed_subgroup {H : set G.obj.type} {h : is_closed_subgroup H}
  (K' : set (sub H).obj.type) [hK : is_closed_subgroup K'] : is_closed_subgroup (set_sub_incl K') :=
omitted

/-- The kernel of a morphism between affine groups is given by the preimage of 1.

More precisely, we can view `f : G ⟶ G'` as a map between the type of `G` and the type of `G'`,
and then take the preimage of `1 : type G'`, using the group structure induced on the type of `G'` -/
def kernel (f : G ⟶ G') : set G.obj.type :=
is_group_hom.ker f.type

/-- The kernel of a morphism is a closed subgroup -/
instance (f : G ⟶ G') : is_closed_subgroup (kernel f) := omitted

/-- A subset of the type of `G` is a normal subgroup if it the kernel of a morphism between
  affine groups. Any normal subgroup is automatically closed. -/
def is_normal_subgroup (s : set G.obj.type) : Prop :=
∃(G' : affine_group K) (f : G ⟶ G'), kernel f = s

/-- The structure of being a normal subgroup -/
def normal_subgroup_structure (s : set G.obj.type) : Type* :=
Σ(G' : affine_group K), {f : G ⟶ G' // kernel f = s }

/-- An affine group `G` is solvable if it is abelian or inductively if there is a morphism
  `ψ : G ⟶ H` such that both `ker(ψ)` and `H` are solvable. -/
-- For some reason this inductive type is very slow to compile if we make this into a `Type`,
-- probably, during the definition of auxilliary declarations. For now, let's have it a Prop,
-- we can turn it into a type later
inductive solvable : affine_group K → Prop
| base {{G : affine_group K}} : G.is_abelian → solvable G
| step {{G H : affine_group K}} (ψ : G ⟶ H) :
  solvable H → solvable (sub (kernel ψ)) → solvable G

/-- A Borel subgroup is a maximal closed connected solvable subgroup of `G` -/
def is_Borel_subgroup (s : set G.obj.type) : Prop :=
is_maximal { t : set G.obj.type |
  ∃(h : is_closed_subgroup t), is_connected t ∧ by exactI solvable (sub t) } s

/-- There is a unique maximal closed subgroup of `G` that is a kernel of a morphism `ψ : G ⟶ A`
  for an abelian group `A` -/
theorem closed_derived_subgroup_unique (H : set G.obj.type) [is_closed_subgroup H] :
  ∃!(s : set G.obj.type), is_maximal { t : set G.obj.type |
    ∃(A : affine_group K) (ψ : sub H ⟶ A), A.is_abelian ∧ t = set_sub_incl (kernel ψ) } s :=
omitted

/-- The closed derived subgroup of `H` is the unique maximal subgroup of `H` that is a kernel of a
  morphism `ψ : H ⟶ A` for an abelian group `A` -/
def closed_derived_subgroup (H : set G.obj.type) [is_closed_subgroup H] : set G.obj.type :=
classical.some (closed_derived_subgroup_unique H)

/-- The closed derived subgroup is a closed subgroup -/
instance closed_derived_subgroup.is_closed_subgroup (H : set G.obj.type) [is_closed_subgroup H] :
  is_closed_subgroup (closed_derived_subgroup H) :=
omitted

open category_theory.limits category_theory.limits.binary_product
local infix ` × `:60 := binary_product
local infix ` ×.map `:90 := binary_product.map

/-- The conjugation map `H₁ × H₂ ⟶ G` given by `(h₁,h₂) ↦ h₁*h₂*h₁⁻¹`-/
def conjugation (H₁ H₂ : set G.obj.type) [is_closed_subgroup H₁] [is_closed_subgroup H₂] :
  (sub H₁).obj × (sub H₂).obj ⟶ G.obj :=
((G.incl H₁).map ≫ diag) ×.map (G.incl H₂).map ≫
product_assoc.hom ≫ 𝟙 G.obj ×.map (product_comm.hom ≫ G.mul) ≫ G.mul
/- The following more explicit definition is hard on the elaborator;
  Probably because of type-class inference for `×` -/
-- calc
--   H₁ × H₂ ⟶ (G × G) × G : ((G.incl H₁).map ≫ diag) ×.map (G.incl H₂).map
--       ... ⟶ G × (G × G) : product_assoc.hom
--       ... ⟶ G × G       : 𝟙 G.obj ×.map (product_comm.hom ≫ G.mul)
--       ... ⟶ G           : G.mul

/-- `C` centralizes `H` if `C × H ⟶ G` given by `(c,h) ↦ c*h*c⁻¹` is equal to the inclusion
`H ⟶ G`. -/
def centralizes (C H : set G.obj.type) [is_closed_subgroup C] [is_closed_subgroup H] : Prop :=
conjugation C H = π₂ ≫ (G.incl H).map

/-- There is a unique maximal closed subgroup of `G` that centralizes `H` -/
theorem centralizer_unique (H : set G.obj.type) [is_closed_subgroup H] :
  ∃!(C : set G.obj.type), is_maximal { C' : set G.obj.type |
    ∃(h : is_closed_subgroup C'), by exactI centralizes C' H } C :=
omitted

/-- The centralizer of `H` is the unique maximal closed subgroup of `G` that centralizes `H` -/
def centralizer (H : set G.obj.type) [is_closed_subgroup H] : set G.obj.type :=
classical.some (centralizer_unique H)

/-- The centralizer is a closed subgroup -/
instance centralizer.is_closed_subgroup (H : set G.obj.type) {h : is_closed_subgroup H} :
  is_closed_subgroup (centralizer H) :=
let ⟨h, _⟩ := (classical.some_spec (centralizer_unique H)).1.1 in h

/-- The center of `G` is the centralizer of `G` as closed subgroup of `G` -/
def center (G : affine_group K) : set G.obj.type :=
centralizer set.univ

/-- `N` normalizes `H` if the conjugation map `N × H ⟶ G` factors through `H` -/
-- this is a slightly different formulation than in the notes
def normalizes (N H : set G.obj.type) [is_closed_subgroup N] [is_closed_subgroup H] : Prop :=
--factors_through (conjugation N H) (G.incl H).map
∃(f : (sub N).obj × (sub H).obj ⟶ (sub H).obj), conjugation N H = f ≫ (G.incl H).map

/-- If `N` normalizes `H` then `N` acts on `H` by conjucation -/
def conjugation_action {N H : set G.obj.type} [is_closed_subgroup N] [is_closed_subgroup H]
  (h : normalizes N H) : group_action (sub N) (sub H).obj :=
⟨classical.some h, omitted, omitted⟩

/-- An affine group is almost simple if it has no proper normal closed connected subgroup.
  Note: by our definition, every normal subgroup is automatically closed -/
def almost_simple (G : affine_group K) : Prop :=
¬∃(T : set G.obj.type), T ≠ set.univ ∧ is_normal_subgroup T ∧ is_connected T

/-- The type of a almost simple affine group is connected -/
lemma connected_space_of_almost_simple : almost_simple G → connected_space G.obj.type :=
omitted

end algebraic_geometry

