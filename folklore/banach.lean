/- 
Frechet derivatives on Banach space
-/

import topology.metric_space
       algebra.module 
       .complex

noncomputable theory

open classical

local attribute [instance] prop_decidable

universes u v

variables (α : Type u) (β : Type v)

section topology

variables [topological_space α]
variables [topological_space β]

class topological_field [field α] extends topological_ring α : Prop :=
(inv_cont : continuous (λ (x : { x // (x : α) ≠ 0 }), (x : α)⁻¹))

class topological_module 
[ring α] [module α  β] [topological_ring α] extends topological_add_group β : Prop :=
(continuous_mul : continuous (λp:α×β, p.1 • p.2))

class t1_topological_vector_space 
[field α] [topological_field α] [t1_space β] [vector_space α β] 
extends topological_module α β : Prop

class has_norm (α : Type u) := 
(norm : α → ℝ)

class multiplicative_norm (α : Type u) [has_norm α] [monoid α] : Prop :=
(mult : ∀ (x y : α), has_norm.norm (x * y) = has_norm.norm x * has_norm.norm y)

#print fields t1_topological_vector_space

--def topological_vector_space.to_vector_space [field α] [topological_field α] [t1_space β] [m : module α β] 
--(tvs : t1_topological_vector_space α β) : vector_space α β := m



end topology




section normed_ring

open has_norm

variables [ring α] [metric_space α] [has_norm α]

class normed_ring : Prop :=
(submult : ∀ (x y : α), norm(x * y) ≤ norm x * norm y)
(norm_dist : ∀ (x y : α), dist x y = norm (x - y))

class multiplicative_normed_ring
(α : Type u) [ring α] [metric_space α] [has_norm α] extends normed_ring α, multiplicative_norm α : Prop

end normed_ring

constant normed_ring.to_topological_field
(α : Type*) [field α] [metric_space α] [has_norm α] [normed_ring α] : topological_field α 
attribute [instance] normed_ring.to_topological_field

section

variables [field α] [metric_space α] [has_norm α] [normed_ring α] 
[vector_space α β] [has_norm β] [metric_space β] [t1_topological_vector_space α β]

class normed_space : Prop :=
(scalar_norm : ∀ (x : α) (y : β), has_norm.norm (x • y) = has_norm.norm x * has_norm.norm y)
(dist_norm: ∀ (x y : β), dist x y = has_norm.norm (x - y))
(triangle : ∀ (x y : β), has_norm.norm(x + y) ≤ has_norm.norm x + has_norm.norm y)
 
structure banach_space 
[complete_space α] [complete_space β]
extends normed_space α β : Prop

end

