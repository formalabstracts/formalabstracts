/- In this file we define the general linear group as an affine group over a discrete field `K`-/
import .affine_variety group_theory.perm.sign ..to_mathlib category_theory.instances.groups

open topological_space function sum finsupp category_theory tensor_product category_theory.limits
universe u

local attribute [instance, priority 1] limits.category_theory.limits.has_limit
  limits.category_theory.limits.has_colimit limits.category_theory.limits.has_colimits
  limits.category_theory.limits.has_limits limits.category_theory.limits.has_limits_of_shape
  limits.category_theory.limits.has_colimits_of_shape
variables (K : Type u) [discrete_field K] {n : ℕ}

noncomputable theory

namespace algebraic_geometry
namespace GL
open mv_polynomial

/-- The `K`-algebra `K[x₀,xᵢⱼ]` for `i,j ∈ {1, ... n}` -/
def GL_aux1 (n : ℕ) : FRAlgebra K :=
FRAlgebra_mv_polynomial.{u 0} K (fin n × fin n ⊕ unit)

/-- Auxiliary definition for the determinant: the graph of a map out of a finite type -/
def det_aux {α β : Type*} [fintype α] [decidable_eq β] (f : α → β) : α × β →₀ ℕ :=
on_finset (finset.univ.product $ finset.univ.image f)
  (λ⟨a, b⟩, if f a = b then 1 else 0)
  (by { rintro ⟨a, b⟩ h, dsimp [det_aux._match_1] at h, cases ite_ne_neg h, simp })

/-- Auxiliary definition for the determinant:
  the graph of a map out of a finite type as an embedding -/
def det_aux2 {α β : Type*} [fintype α] [decidable_eq β] : (α → β) ↪ α × β →₀ ℕ :=
⟨det_aux, omitted⟩

/-- Auxiliary definition for the determinant: the function that turns an equivalence into
  a monomial in a polynomial ring over one extra variable. -/
def det_aux3 {α β : Type*} [fintype α] [decidable_eq α] [decidable_eq β] :
  (α ≃ β) ↪ α × β ⊕ unit →₀ ℕ :=
equiv.equiv_embedding_fun.trans $ det_aux2.trans $ finsupp_embedding_finsupp_left sum.embedding_inl

/-- We define the determinant as a multivariate polynomial follows:
* We can embed permutations `fin n ≃ fin n` into `fin n × fin n →₀ ℕ` using the
  characteristic map of the graph of the function.
* If a monomial corresponds to a permutation, then its coefficient is the sign of the permutation,
  otherwise it is `0`. -/
def det (n : ℕ) : GL_aux1 K n :=
emb_domain det_aux3 $ equiv_fun_on_fintype.inv_fun $ λ e, int.cast $ equiv.perm.sign e

/-- The element `x₀ * det(xᵢⱼ) - 1` in `K[x₀,xᵢⱼ]` by which we quotient to obtain `GL(n)` -/
def GL_element (n : ℕ) : GL_aux1 K n :=
X (inr ⟨⟩) * det K n - 1

/-- The ideal spanned by `x₀ * det(xᵢⱼ) - 1` is radical -/
lemma radical_ideal_span_det (n : ℕ) :
  (ideal.span ({ GL_element K n } : set (GL_aux1 K n))).is_radical :=
omitted

/-- The ideal spanned by `x₀ * det(xᵢⱼ) - 1` as a radical ideal -/
def GL_aux (n : ℕ) : ideal.radical_ideal (GL_aux1 K n) :=
⟨(ideal.span ({ GL_element K n } : set (GL_aux1 K n))), by apply radical_ideal_span_det K n⟩

/-- The general linear group is defined as `K[x₀,xᵢⱼ]/(x₀ * det(xᵢⱼ) - 1)` -/
def GL_op (n : ℕ) : FRAlgebra K :=
⟨K, (GL_aux K n).val.quotient⟩

/-- The general linear group as an affine variety -/
def GL_var (n : ℕ) : affine_variety K :=
op (GL_op K n)

variable {K}
section
set_option class.instance_max_depth 80
/-- The (opposite of the) multiplication on `GL(n)`. It uses the formula for matrix multiplcation,
  sending `xᵢⱼ` to `Σₖ xᵢₖ ⊗ xₖⱼ`. It sends `x₀` to `x₀ ⊗ x₀` -/
def GL_mul_op : GL_op K n ⟶ FRAlgebra_tensor (GL_op K n) (GL_op K n) :=
algebra.quotient.lift
  begin
    refine alg_hom.comp (tensor_functor (algebra.quotient.mk _) (algebra.quotient.mk _)) _,
    refine aeval₂ _,
    rintro (⟨i,j⟩|⟨⟩),
    { refine (finset.univ : finset (fin n)).sum _, intro k,
      exact tmul K (X $ inl ⟨i, k⟩) (X $ inl ⟨k, j⟩) },
    { exact tmul K (X $ inr ⟨⟩) (X $ inr ⟨⟩) }
  end
 omitted
end

/-- The `(i,j)`-minor is the polynomial that is obtained by taking the formula for the determinant,
  but skipping row `i` and column `j`. -/
def minor (i j : fin n) : GL_aux1 K n :=
begin
  cases n with n, apply fin_zero_elim i,
  exact rename (sum.map (prod.map (fin.succ_above i) (fin.succ_above j)) id) (det K n)
end

/-- The (opposite of the) inversion on `GL(n)`. The inverse sends `xᵢⱼ` to
  `(-1) ^ (i + j)` times the transpose of the `(i,j)`-minor. It sends `x₀` to `det(xᵢⱼ)` -/
def GL_inv_op : GL_op K n ⟶ GL_op K n :=
algebra.quotient.functor
  begin
    refine aeval₂ _,
    rintro (⟨i,j⟩|⟨⟩),
    { exact (-1) ^ (i.val + j.val) * minor j i },
    { exact det K n }
  end
 omitted

/-- The (opposite of the) unit in `GL(n)` -/
def GL_one_op : GL_op K n ⟶ FRAlgebra_id K :=
algebra.quotient.lift
  begin
    refine aeval₂ _,
    rintro (⟨i,j⟩|⟨⟩),
    { exact if i = j then 1 else 0 },
    { exact 1 }
  end
 omitted

variable (K)
/-- The general linear group as an affine group -/
def GL (n : ℕ) : affine_group K :=
{ obj := GL_var K n,
  mul := GL_mul_op.op,
  mul_assoc := omitted,
  one := GL_one_op.op,
  one_mul := omitted,
  mul_one := omitted,
  inv := GL_inv_op.op,
  mul_left_inv := omitted }

/-- A torus is an `r`-fold product of `GL(1)` -/
def torus (r : ℕ) : affine_group K := category.pow (GL K 1) r

/-- The multiplicative affine group is `torus K 1` -/
@[reducible] def Gm : affine_group K := torus K 1

variable {K}

/- The map `n ↦ X ^ n`. It sends `(-n)` to `(X⁻¹)^n` for a natural number n -/
def X_pow : ℤ → (unop (Gm K).1).β
| (int.of_nat n) := ideal.quotient.mk _ (monomial (single (inl ⟨0, 0⟩) n) 1)
| -[1+n]         := ideal.quotient.mk _ (monomial (single (inr ⟨⟩) (n+1)) 1)

/-- Every group morphism `Gm ⟶ Gm` sends the variable `X` to `X^n` for some integer `n`. -/
def deg_aux (ϕ : Gm K ⟶ Gm K) :
  ∃!(n : ℤ), ϕ.map.unop.to_fun (ideal.quotient.mk _ $ X $ inl ⟨0, 0⟩) = X_pow n :=
omitted

/-- The degree of a group morphism `Gm K ⟶ Gm K` is the unique number `n` such that it sends
`X` to `X^n` -/
def deg (ϕ : Gm K ⟶ Gm K) : ℤ :=
classical.the _ (deg_aux ϕ)

instance torus1.is_abelian : (Gm K).is_abelian := omitted

lemma nonzero_determinant (p : (GL_var K n).type) :
  p.to_fun (ideal.quotient.mk _ (det K n)) ≠ (0 : K) :=
omitted

/-- The torus is an abelian group -/
instance is_abelian_torus (r : ℕ) : (torus K r).is_abelian := omitted

variable {G : affine_group K}

/-- A maximal torus is a closed subgroup of `G` that is isomorphic to `torus K r`
  with `r` maximal. -/
class is_maximal_torus (T : set G.obj.type) extends is_closed_subgroup T : Prop :=
(max_torus : ∃(n : ℕ), nonempty (sub T ≅ torus K n) ∧
  is_maximal { m : ℕ | ∃(s : set G.obj.type) (h : is_closed_subgroup s),
  by exactI nonempty (sub s ≅ torus K m) } n)

def is_maximal_torus.elim {T : set G.obj.type} (h₂ : is_maximal_torus T) :=
is_maximal_torus.max_torus T

instance is_maximal_torus.is_abelian (T : set G.obj.type) [is_maximal_torus T] :
  (sub T).is_abelian := omitted

/- The rank of a maximal torus -/
def is_maximal_torus.rank (T : set G.obj.type) [h : is_maximal_torus T] : ℕ :=
classical.take_arbitrary_such_that (λ n, n) h.elim omitted

/-- Every group has a maximal torus -/
lemma has_maximal_torus (G : affine_group K) : ∃(T : set G.obj.type), is_maximal_torus T :=
omitted

/-- The rank of `G` is the number `n` such that `T ≅ torus n`
  where `T` is any maximal torus of `G`. -/
def rank (G : affine_group K) : ℕ :=
classical.take_arbitrary (λ ⟨T, hT⟩, by exactI is_maximal_torus.rank T :
  { T : set (G.obj.type) // is_maximal_torus T} → ℕ)
  (subtype.nonempty $ has_maximal_torus G) omitted

/-- The character group `X^*(T)` of `T` consists of group morphisms into `Gm K` -/
@[reducible] def character_group (T : set G.obj.type) [is_closed_subgroup T] : Type* :=
sub T ⟶ Gm K

/-- The character group froms an abelian group -/
example (T : set G.obj.type) [is_closed_subgroup T] : comm_group (character_group T) :=
infer_instance

open category_theory.instances
/-- The character group is a free group on `rank G` variables -/
lemma free_character_group (T : set G.obj.type) [is_maximal_torus T] :
  nonempty $ (mk_ob $ character_group T : Group) ≅
    mk_ob (multiplicative $ free_abelian_group $ ulift $ fin $ rank G) :=
omitted

/-- As a more concrete example, we give the underlying functions of the isomorphism between
 `Gm K ⟶ Gm K` and the free abelian group on a single generator -/
def hom_torus1 : (mk_ob $ (Gm K) ⟶ Gm K : Group) ≅
  mk_ob (multiplicative $ free_abelian_group punit) :=
{ hom := ⟨λ ϕ, free_abelian_group.of ⟨⟩ ^ deg ϕ, omitted⟩,
  inv := ⟨λ n, show additive $ Gm K ⟶ Gm K, from n.lift (λ x, 𝟙 _), omitted⟩,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted }

/-- The cocharacter group `X_*(T)` of `T` consists of group morphisms from `Gm K` -/
@[reducible] def cocharacter_group (T : set G.obj.type) [is_closed_subgroup T] : Type* :=
Gm K ⟶ sub T

example (T : set G.obj.type) [is_maximal_torus T] : comm_group (cocharacter_group T) :=
infer_instance

/-- The cocharacter group is a free group on `rank G` variables -/
lemma free_cocharacter_group (T : set G.obj.type) [is_maximal_torus T] :
  nonempty $ (mk_ob $ cocharacter_group T : Group) ≅
    mk_ob (multiplicative $ free_abelian_group $ ulift $ fin $ rank G) :=
omitted

/-- There is a pairing between the character group and the cocharacter group of `T`. -/
def pair {T : set G.obj.type} [is_closed_subgroup T]
  (l : character_group T) (r : cocharacter_group T) : ℤ :=
deg $ r ≫ l

end GL
-- TODO: pair is nondegenerate and bilinear

variables (K)
namespace Ga
open polynomial GL
/-- The underlying affine variety of the additive affine group is the variety whose coordinate ring
  is `K[x]` -/
def Ga_var : affine_variety K :=
op $ FRAlgebra_polynomial K

variables {K}
/-- The (opposite of the) multiplication on `Ga`. It sends `x` to `x ⊗ 1 + 1 ⊗ x` -/
def Ga_mul_op :
  FRAlgebra_polynomial K ⟶ FRAlgebra_tensor (FRAlgebra_polynomial K) (FRAlgebra_polynomial K) :=
aeval _ _ $ tmul K X 1 + tmul K 1 X

/-- The (opposite of the) inversion on `Ga`. It sends `x` to `-x` -/
def Ga_inv_op : FRAlgebra_polynomial K ⟶ FRAlgebra_polynomial K :=
aeval _ _ $ -X

/-- The (opposite of the) unit in `Ga` -/
def Ga_one_op : FRAlgebra_polynomial K ⟶ FRAlgebra_id K :=
aeval _ _ 0

variables (K)
/-- The additive affine group -/
def Ga : affine_group K :=
{ obj := Ga_var K,
  mul := Ga_mul_op.op,
  mul_assoc := omitted,
  one := Ga_one_op.op,
  one_mul := omitted,
  mul_one := omitted,
  inv := Ga_inv_op.op,
  mul_left_inv := omitted }

local infix ` × `:60 := limits.binary_product
/-- The group `Gm` acts on `Ga`. -/
def mul_add_action : group_action (Gm K) (Ga K).obj :=
⟨(show FRAlgebra_polynomial K ⟶ FRAlgebra_tensor (GL_op K 1) (FRAlgebra_polynomial K),
  from aeval _ _ $ tmul _ (ideal.quotient.mk _ $ mv_polynomial.X $ inl $ ⟨0, 0⟩) X).op,
  omitted, omitted⟩

end Ga
open GL Ga
variables {K}

variables {G : affine_group K} (B T : set G.obj.type) [is_closed_subgroup B] [is_maximal_torus T]

local infix ` × `:60 := limits.binary_product
local infix ` ×.map `:90 := binary_product.map

structure positive_root_space :=
(X : set G.obj.type)
(hX : is_closed_subgroup X)
(hXU : X ⊆ closed_derived_subgroup B)
(f : sub X ≅ Ga K)
(hTX : normalizes T X)

attribute [instance] positive_root_space.hX

variables {B T}
def is_positive_root (X : positive_root_space B T) (l : character_group T) : Prop :=
(conjugation_action X.hTX).map = l.map ×.map X.f.hom.map ≫ (mul_add_action K).map ≫ X.f.inv.map

-- def positive_root (X : positive_root_space B T) : Type* :=
-- { l : character_group T // is_positive_root X l }

lemma unique_positive_root (hG : almost_simple G) (hB : is_Borel_subgroup B) (hTB : T ⊆ B)
  (X : positive_root_space B T) : ∃!(l : character_group T), is_positive_root X l :=
omitted

variables (B T)
def Phi_plus : set (character_group T) :=
{ l : character_group T | ∃(X : positive_root_space B T), is_positive_root X l }

notation `Φ⁺` := Phi_plus

lemma finite_Phi_plus (hG : almost_simple G) (hB : is_Borel_subgroup B) (hTB : T ⊆ B) :
  set.finite (Φ⁺ B T) := omitted

variables {B T}
variables (α : character_group T)
local notation `M'` := closed_derived_subgroup $ centralizer $ kernel $ α

lemma almost_simple_M' (hG : almost_simple G) (hB : is_Borel_subgroup B) (hTB : T ⊆ B)
  (hα : α ∈ Φ⁺ B T) : almost_simple $ sub M' :=
omitted

def is_positive_coroot (αv : cocharacter_group T) : Prop :=
∃(S : set (sub M').obj.type) (hS₁ : is_maximal_torus S),
  by exactI factors_through αv.map ((sub T).incl $ set_sub_incl S).map ∧ GL.pair α αv = 2

lemma unique_positive_coroot (hG : almost_simple G) (hB : is_Borel_subgroup B) (hTB : T ⊆ B)
  (hα : α ∈ Φ⁺ B T) : ∃!(αv : cocharacter_group T), is_positive_coroot α αv :=
omitted

variables (B T)
def positive_coroots : set (cocharacter_group T) :=
{ αv : cocharacter_group T | ∃(α ∈ Φ⁺ B T), is_positive_coroot α αv }

-- todo: move
def cone {α} [comm_monoid α] [decidable_eq α] (s : set α) : set α :=
{ x : α | ∃(t : finset α) (a : α → ℕ), ↑t ⊆ s ∧ t.prod (λ(y : α), y ^ a y) = x }

variables {B T}

section
local attribute [instance, priority 0] classical.prop_decidable
lemma unique_simple_roots (hG : almost_simple G) (hB : is_Borel_subgroup B) (hTB : T ⊆ B) :
  ∃!(Δ : set (character_group T)), Δ ⊆ Φ⁺ B T ∧ Φ⁺ B T ⊆ cone Δ :=
omitted
end

def simple_roots (hG : almost_simple G) (hB : is_Borel_subgroup B) (hTB : T ⊆ B) :
  set (character_group T) :=
classical.the _ $ unique_simple_roots hG hB hTB

end algebraic_geometry
