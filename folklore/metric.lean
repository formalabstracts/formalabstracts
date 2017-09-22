/-
Metric Spaces following HOL Light.
A topology and metric encompass the full type, not a subset.
-/

import data.set meta_data data.list data.vector .real_axiom

noncomputable theory

namespace metric

open set classical nat int list vector real_axiom

local attribute [instance] prop_decidable

universes u v w

variables {α : Type} { β : Type}

def preimage (f : α → β) (s : set β) :=
{ x | f x ∈ s}

-- perhaps this should be a default coercion
instance coe_set {α : Type} {β : Type} [has_coe α β] : has_coe (set α) (set β) := 
⟨ (λ S : set α, λ b : β, ∃ a ∈ S, has_coe.coe β a = b) ⟩

-- topology 

structure topological_space (α : Type u) : Type u :=
(is_open : set(set α))
(is_open_univ : univ ∈ is_open)
(is_open_empty : ∅ ∈ is_open)
(is_open_inter : ∀ s ∈ is_open, ∀ t ∈ is_open, s ∩ t ∈ is_open)
(is_open_sUnion : ∀ k ⊆ is_open, ⋃₀ k ∈ is_open)

attribute [class] topological_space

variables (X : topological_space α) (Y : topological_space β) (S : set α)

def open_in := S ∈ X.is_open

def closed_in := (- S) ∈ X.is_open

unfinished discrete_topological_space_exists : 
Π (α : Type), (∃ X : topological_space α, X.is_open = (λ ( x : set α), true)) :=
{ description := "on each type there exists a unique discrete topological_space" }

def discrete_topological_space {α : Type} : topological_space α :=
classical.some (discrete_topological_space_exists α)

unfinished subtopological_space_exists : 
Π {α : Type} (X : topological_space α) (u : set α), 
(∃ (Y : topological_space (subtype u)), { Uy | ∃ Ux ∈ X.is_open, Ux ∩ u = Uy } = Y.is_open) :=
{ description := "for each topological_space and subset, there exists a unique induced subtopological_space" }

def subtopological_space : topological_space (subtype S) := 
classical.some (subtopological_space_exists X S)

def closure_of : set α :=
{ x | ∀ t,  x ∈ t ∧ open_in X t → ∃ y ∈ S, y ∈ t }

def interior_of : set α :=
{ x | ∃ t ∈ X.is_open, x ∈ t ∧ t ⊆ S }

def frontier_of : set α :=
closure_of X S \ interior_of X S

-- skipping material on nets, do it with filters instead...

structure metric_space (α : Type) : Type :=
(d : α → α → ℝ)
(non_negative : ∀ x y, 0 ≤ d x y)
(zero : ∀ x y, d x y = 0 → (x = y))
(symmetry : ∀ x y, d x y = d y x)
(triangle_ineq : ∀ x y z, d x z ≤ d x y + d y z)

variable (m : metric_space α)

-- open metric_space ball % todo mball -> ball
def mball (x : α) (r : ℝ) : (set α) :=
{y : α | m.d x y < r}

unfinished submetric_exists :
Π {α : Type} (m: metric_space α) (s: set α),
(∃ (X : metric_space (subtype s)), ∀ x y, X.d x y = m.d x y) :=
{ description := "a metric uniquely restricts to a metric on each subset" }

def submetric (s : set α) : (metric_space (subtype s)) :=
classical.some (submetric_exists m s)

unfinished mtopological_space_exists :
Π {α : Type} (m : metric_space α),
(∃ (X : topological_space α), X.is_open = {u | ∀ x ∈ u, ∃ r > 0, mball m x r ⊆ u}) :=
{ description := "every metric determines a unique topological_space" }

def mtopological_space : (topological_space α) :=
classical.some (mtopological_space_exists m)

-- closed metric_space ball
def mcball (x : α) (r : ℝ) : (set α) :=
{y : α | m.d x y ≤ r}

unfinished discrete_metric_exists :
Π (α : Type),
(∃ (X : metric_space α), ∀ x y, X.d x y = if x=y then 0 else 1) :=
{ description := "the discrete metric is a metric" }

def discrete_metric (α : Type) : (metric_space α) :=
classical.some (discrete_metric_exists α)

def msphere (x : α) (r : ℝ) : (set α) :=
{y : α | m.d x y = r}

def mbounded :=
(∃ x r, S ⊆ mcball m x r)

def compact_in :=
(∀ U, (∀ u ∈ U, open_in X u) ∧ (S ⊆ ⋃₀ U) → (∃ V, finite V ∧ V ⊆ U ∧ S ⊆ ⋃₀ V))

def compact_space :=
compact_in X univ

def connected_space :=
(¬(∃ e1 e2, open_in X e1 ∧ open_in X e2 ∧ e1 ∪ e2 = univ  ∧ e1 ∩ e2 = ∅ 
  ∧ ¬(e1 = ∅) ∧ ¬(e2 = ∅)))

def connected_in :=
connected_space (subtopological_space X S)

def neighbourhood_base_at (x : α) (P : set (set α)) (X : topological_space α) : Prop :=
(∀ w, open_in X w ∧ x ∈ w → ∃ u v, open_in X u ∧ v ∈ P ∧ x ∈ u ∧ u ⊆ v ∧ v ⊆ w) 

def neighbourhood_base_of (P : set(set α)) (X : topological_space α) : Prop :=
(∀ x, neighbourhood_base_at x P X)

def metrizable_space :=
(∃ m, X = mtopological_space m)

-- T1 spaces
def t1_space :=
(∀ x y, ¬(x=y) → ∃ u, open_in X u ∧ x ∈ u ∧ ¬(y ∈ u))

def hausdorff_space :=
(∀ x y, ¬(x=y) → ∃ u v, open_in X u ∧ open_in X v ∧ x ∈ u ∧ x ∈ v ∧ disjoint u v)

def regular_space :=
(∀ c a, closed_in X c ∧ ¬(a ∈ c) → ∃ u v, open_in X u ∧ open_in X v ∧ a ∈ u ∧ c ⊆ v ∧ disjoint u v)

def locally_compact_space :=
(∀ x, ∃ u k, open_in X u ∧ compact_in X k ∧ x ∈ u ∧ u ⊆ k)

def normal_space :=
(∀ s t, closed_in X s ∧ closed_in X t ∧ disjoint s t →
(∃ u v, open_in X u ∧ open_in X v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v))


-- metric on ℝ

def real_open (s : set ℝ) :=
(∀ x ∈ s, ∃ e > 0, ∀ x', real_abs(x' - x) < e → x' ∈ s)

def real_closed (s : set ℝ) :=
real_open (univ \ s)

unfinished euclideanreal_exists :
(∃ X : topological_space ℝ, X.is_open = real_open) :=
{ description := "the Euclidean space topological_space exists" }

def euclideanreal : topological_space ℝ :=
classical.some euclideanreal_exists

unfinished real_euclidean_metric_exists :
(∃ m : metric_space ℝ, ∀ x y, m.d x y = real_abs(x - y)) :=
{ description := "the Euclidean metric exists" }

def real_euclidean_metric : metric_space ℝ :=
classical.some real_euclidean_metric_exists

def real_bounded (s : set ℝ) : Prop :=
(∃ r, ∀ x ∈ s, real_abs(x) ≤ r)

def real_compact (s : set ℝ) : Prop :=
compact_in euclideanreal s

-- cauchy

variable (f : α → β)

def cauchy_in (s : ℕ → α) :=
(∀ e > 0, ∃ N, ∀ n n', N ≤ n ∧ N ≤ n' → m.d (s n) (s n') < e)

def totally_bounded_in :=
(∀ e > 0, ∃ k, finite k ∧ k ⊆ S ∧ S ⊆ ⋃₀ { b | ∃ x ∈ k, b = mball m x e })

def continuous_at (x : α) :=
(∀ v, open_in Y v ∧ f x ∈ v → ∃ u, open_in X u ∧ x ∈ u ∧ (∀ y ∈ u, f y ∈ v))

def continuous_map :=
(∀ u, open_in Y u → open_in X (preimage f u))

def open_map :=
(∀ u, open_in X u → open_in Y (image f u))

def closed_map :=
(∀ u, closed_in X u → closed_in Y (image f u))

def lipschitz_continuous_map (m1 : metric_space α) (m2 : metric_space β) (f : α → β) :=
(∃ b, ∀ x y, m2.d (f x) (f y) ≤ b * m1.d x y)

def uniformly_continuous_map (m1 : metric_space α) (m2 : metric_space β) (f : α → β) :=
(∀ e > 0, ∃ d > 0, ∀ x x', m1.d x' x < d → m2.d (f x') (f x) < e)

def cauchy_continuous_map (m1 : metric_space α) (m2 : metric_space β) (f : α → β) :=
(∀ x, cauchy_in m1 x → cauchy_in m2 (f ∘ x))


end metric

