/- In this file we define the general linear group as an affine group over a discrete field `K`-/
import .affine_variety group_theory.perm.sign ..to_mathlib category_theory.instances.groups

open topological_space function sum finsupp category_theory tensor_product category_theory.limits
universe u

variables (K : Type u) [discrete_field K] {n : ℕ}

local attribute [instance, priority 1500] algebra.mv_polynomial
--  field.to_comm_ring --tensor_product.ring tensor_product.comm_ring tensor_product.algebra
noncomputable theory

namespace algebraic_geometry
/-- The `K`-algebra `K[x₀,xᵢⱼ]` for `i,j ∈ {1, ... n}` -/
def GL_aux1 (n : ℕ) : FRAlgebra K :=
{ β := mv_polynomial (fin n × fin n ⊕ unit) K,
  algebra := { finitely_generated := omitted,
               reduced := omitted } }

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
mv_polynomial.X (inr ⟨⟩) * det K n - 1

/-- The ideal spanned by `x₀ * det(xᵢⱼ) - 1` is radical -/
lemma radical_ideal_span_det (n : ℕ) :
  (ideal.span ({ GL_element K n } : set (GL_aux1 K n))).is_radical :=
omitted

/-- The ideal spanned by `x₀ * det(xᵢⱼ) - 1` as a radical ideal -/
def GL_aux (n : ℕ) : ideal.radical_ideal (GL_aux1 K n) :=
⟨(ideal.span ({ GL_element K n } : set (GL_aux1 K n))), by apply radical_ideal_span_det K n⟩

/-- The general linear group is defined as `K[x₀,xᵢⱼ]/(x₀ * det(xᵢⱼ) - 1)` -/
def GLop (n : ℕ) : FRAlgebra K :=
⟨K, (GL_aux K n).val.quotient⟩

/-- The general linear group as an affine variety-/
def GL (n : ℕ) : affine_variety K :=
op (GLop K n)

variable {K}
section
set_option class.instance_max_depth 80
/-- The (opposite of the) multiplication on `GL(n)`. It uses the formula for matrix multiplcation,
  sending `xᵢⱼ` to `Σₖ xᵢₖ ⊗ xₖⱼ`. It sends `x₀` to `x₀ ⊗ x₀` -/
def GL_mul_op : GLop K n ⟶ FRAlgebra_tensor (GLop K n) (GLop K n) :=
algebra.quotient.lift
  begin
    refine alg_hom.comp (tensor_functor (algebra.quotient.mk _) (algebra.quotient.mk _)) _,
    refine mv_polynomial.aeval₂ _,
    rintro (⟨i,j⟩|⟨⟩),
    { refine (finset.univ : finset (fin n)).sum _, intro k,
      exact tmul K (mv_polynomial.X $ inl ⟨i, k⟩) (mv_polynomial.X $ inl ⟨k, j⟩) },
    { exact tmul K (mv_polynomial.X $ inr ⟨⟩) (mv_polynomial.X $ inr ⟨⟩) }
  end
 omitted
end

/- The `(i,j)`-minor is the polynomial that is obtained by taking the formula for the determinant,
  but skipping row `i` and column `j`. -/
def minor (i j : fin n) : GL_aux1 K n :=
begin
  cases n with n, apply fin_zero_elim i,
  exact mv_polynomial.rename (sum.map (prod.map (fin.succ_above i) (fin.succ_above j)) id) (det K n)
end

/-- The (opposite of the) inversion on `GL(n)`. The inverse sends `xᵢⱼ` to
  `(-1) ^ (i + j)` times the transpose of the `(i,j)`-minor. It sends `x₀` to `det(xᵢⱼ)` -/
def GL_inv_op : GLop K n ⟶ GLop K n :=
algebra.quotient.functor
  begin
    refine mv_polynomial.aeval₂ _,
    rintro (⟨i,j⟩|⟨⟩),
    { exact (-1) ^ (i.val + j.val) * minor j i },
    { exact det K n }
  end
 omitted

/-- The (opposite of the) unit in `GL(n)` -/
def GL_one_op : GLop K n ⟶ FRAlgebra_id K :=
algebra.quotient.lift
  begin
    refine mv_polynomial.aeval₂ _,
    rintro (⟨i,j⟩|⟨⟩),
    { exact if i = j then 1 else 0 },
    { exact 1 }
  end
 omitted

variable (K)
/-- The general linear group as an affine group -/
def GLgr (n : ℕ) : affine_group K :=
{ obj := GL K n,
  mul := GL_mul_op.op,
  mul_assoc := omitted,
  one := GL_one_op.op,
  one_mul := omitted,
  mul_one := omitted,
  inv := GL_inv_op.op,
  mul_left_inv := omitted }

/-- A torus is an `r`-fold product of `GL(1)` -/
def torus (r : ℕ) : affine_group K := category.pow (GLgr K 1) r

variable {K}
lemma nonzero_determinant (p : (GL K n).type) :
  p.to_fun (ideal.quotient.mk _ (det K n)) ≠ (0 : K) :=
omitted

/-- The torus is an abelian group -/
instance is_abelian_torus (r : ℕ) : (torus K r).is_abelian := omitted

variable {G : affine_group K}

/-- A maximal torus is a closed subgroup of `G` that is isomorphic to `torus K r`
  with `r` maximal. -/
-- question: is T required to be closed?
def is_maximal_torus (T : set G.obj.type) [is_closed_subgroup T] : Prop :=
∃(n : ℕ), nonempty (sub T ≅ torus K n) ∧
is_maximal { m : ℕ | ∃(s : set G.obj.type) (h : is_closed_subgroup s),
  by exactI nonempty (sub s ≅ torus K m) } n

/-- Every group has a maximal torus -/
lemma has_maximal_torus (G : affine_group K) : ∃(T : set G.obj.type) (h : is_closed_subgroup T),
  by exactI is_maximal_torus T :=
omitted

/-- The rank of `G` is the number `n` such that `T ≅ torus n`
  where `T` is any maximal torus of `G`. -/
def rank (G : affine_group K) : ℕ :=
classical.some $ classical.some_spec $ classical.some_spec $ has_maximal_torus G

@[reducible] def character_group (T : set G.obj.type) [is_closed_subgroup T] : Type* :=
sub T ⟶ torus K 1

example (T : set G.obj.type) [is_closed_subgroup T] : comm_group (character_group T) :=
by apply_instance

open category_theory.instances
lemma free_character_group (T : set G.obj.type) [is_closed_subgroup T] (h : is_maximal_torus T) :
  nonempty $ (mk_ob $ character_group T : Group) ≅
    mk_ob (multiplicative $ free_abelian_group $ ulift $ fin $ rank G) :=
omitted

@[reducible] def cocharacter_group (T : set G.obj.type) [is_closed_subgroup T] : Type* :=
torus K 1 ⟶ sub T

def pair {T : set G.obj.type} [is_closed_subgroup T]
  (l : character_group T) (r : cocharacter_group T) : ℤ :=
sorry

-- def affine_variety.type.eval {X : affine_variety K} (a : affine_variety.type X)
--   (x :  : Type u :=
-- (affine_variety.type_functor K).obj X


end algebraic_geometry
