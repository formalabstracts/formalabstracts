/- 
Frechet derivatives on Banach space
-/

import order.filter data.set meta_data data.list data.vector
       topology.real topology.continuity topology.metric_space
       algebra.module data.finset.basic  -- .metric
       .banach

noncomputable theory

open set filter classical

local attribute [instance] prop_decidable

universes u v

section


variables (α : Type u) [topological_space α ]
variables (β : Type v) [topological_space β ]

class topological_field [field α] extends topological_ring α  :=
(inv_cont : continuous (λ (x : { x // (x : α) ≠ 0 }), (x : α)⁻¹))

class topological_module [ring α] [module α  β] [topological_ring α] extends topological_add_group β  :=
(continuous_mul : continuous (λp:α×β, p.1 • p.2))

end

variables (α : Type*) (β : Type*) [topological_space α] [ring α] [topological_ring α]
  [topological_space β] [module α β]
variable (t : topological_module α β)

--set_option trace.class_instances true
--set_option class.instance_max_depth 100

section
variables {α : Type u} (β : Type v) [field α]

-- valuation on a field.
-- see Berkovich, page 2, http://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf
class valuation extends metric_space α :=
(val : α → ℝ)
(nonneg : ∀ x, val x ≥ 0)
(multiplicative : ∀ x y, val (x * y) = val x * val y)
(triangle: ∀ x y, val (x + y) ≤ val x + val y)






end

section

variables (α : Type u) (β : Type v) 

class has_norm (α : Type u) := 
(norm : α → ℝ)

class multiplicative_norm (α : Type u) [has_norm α] [monoid α] :=
(mult : ∀ (x y : α), has_norm.norm (x * y) = has_norm.norm x * has_norm.norm y)

class normed_ring (α : Type u) extends ring α, metric_space α, has_norm α :=
(submult : ∀ x y, norm(x * y) ≤ norm x * norm y)
(norm_dist : ∀ (x y : α), dist x y = norm (x - y))

class multiplicative_normed_ring extends normed_ring α, multiplicative_norm α

variables [ring α] [normed_ring α] [topological_space α] [topological_ring α]
variables [module α β]

class normed_module extends metric_space β, topological_module α β, has_norm β :=
(homogeneity : ∀ (c : α) (v : β), norm(c • v) = has_norm.norm c * norm v)
(norm_dist : ∀ v w, dist v w = norm (v - w))

end

#check complete_space

axiom exists_real_multiplicative_normed_field :
(∃!p : multiplicative_normed_field ℝ, p.norm = real_abs)

instance real_multiplicative_normed_field :=
classical.some exists_real_multiplicative_normed_field

axiom exists_complex_multiplicative_normed_field :
(∃!p : multiplicative_normed_field ℂ, p.norm = complex.norm)

instance complex_multiplicative_normed_field :=
classical.some exists_complex_multiplicative_normed_field

class banach_space (α : Type u) (β : Type v) [multiplicative_normed_field α] extends normed_space α β, complete_metric_space β

class real_banach_space (β : Type v) extends banach_space ℝ β

def linear { α : Type u} {β : Type v} {γ : Type w} [field α] [vector_space α β] [vector_space α γ] (f : β → γ) : Prop :=
(∀ (x : α) (v : β), f (x • v) = x • f v) ∧
(∀ v w, f (v + w) = f v + f w)

-- bounded in a topological vector space
--def bounded { α : Type u} [topological_vector_space α]




/-
class complex_vector_space β extends vector_space ℂ β

class  complex_normed_space (β : Type u) extends complex_vector_space β :=
(norm : β → ℝ)
(positivity : ∀ v, norm v ≥ 0)
(norm0 : ∀ v, norm v = 0 ↔ v = 0)
(homogeneity : ∀ (c : ℂ) (v : β), norm(c  • v) = complex.norm c * norm v)
(triangle_inequality : ∀ v w, norm(v + w) ≤ norm v + norm w)
-/















end derivative
