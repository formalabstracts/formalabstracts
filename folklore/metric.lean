/-
Metric Spaces.
The starting point was the HOL Light library, but many changes 
and additions have been made.


-/

import order.filter data.set meta_data data.list data.vector
       topology.topological_space topology.real 
       .complex -- .measure_theory 


noncomputable theory

namespace metric

open set filter classical nat int list vector real complex

local attribute [instance] prop_decidable

universes u v w

variables {α : Type u} { β : Type v}

instance coe_set {α : Type u} {β : Type u} [has_coe α β] : has_coe (set α) (set β) := 
⟨ (λ S : set α, λ b : β, ∃ a ∈ S, has_coe.coe β a = b) ⟩

-- topology 

structure topological_space (α : Type u) : Type u :=
(is_open : set(set α))
(is_open_univ : univ ∈ is_open)
(is_open_inter : ∀ s ∈ is_open, ∀ t ∈ is_open, s ∩ t ∈ is_open)
(is_open_sUnion : ∀ k ⊆ is_open, ⋃₀ k ∈ is_open)

attribute [class] topological_space

variables (X : topological_space α) (Y : topological_space β) (S : set α)

def is_open := S ∈ X.is_open

def is_closed := (- S) ∈ X.is_open

def generated_topology (A : set (set α)) :=
⋂₀ {σ : set (set α) | ∃ (X : topological_space α), X.is_open = σ ∧ A ⊆ σ ∧ univ ∈ σ}

axiom exists_generated_topology  :
Π (A : set (set α)),
(∃! (X:topological_space α), X.is_open = generated_topology A)

def mk_topological_space (A : set (set α)) :=
classical.some (exists_generated_topology A)

def cartesian { α : Type u} {β : Type v} (Xa : set α) (Xb : set β) : set (α × β) :=
{ ab : α × β | let (a,b) := ab in a ∈ Xa ∧ b ∈ Xb }

def product_topology { α : Type u } {β : Type v} [Xa : topological_space α] [Xb : topological_space β] : topological_space (α × β) :=
mk_topological_space 
{ ab : set (α × β) |  ∃ a b, ab = cartesian a b ∧ is_open Xa a ∧ is_open Xb b}

-- unfinished does not allow universes, see comments in real_axiom.lean:

axiom  discrete_topological_space_exists :
Π (α : Type u), (∃! X : topological_space α, X.is_open = (λ ( x : set α), true)) 

-- { description := "on each type there exists a unique discrete topological_space" }

def discrete_topological_space {α : Type u} : topological_space α :=
classical.some (discrete_topological_space_exists α)

axiom induced_space_exists : 
Π {α : Type u} (X : topological_space α) (u : set α), 
(∃! (Y : topological_space (subtype u)), { Uy | ∃ Ux ∈ X.is_open, Ux ∩ u = Uy } = Y.is_open) 
-- :=
-- { description := "for each topological_space and subset, there exists a unique induced induced_space" }

def induced_space : topological_space (subtype S) := 
classical.some (induced_space_exists X S)

def closure : set α :=
{ x | ∀ t,  x ∈ t ∧ is_open X t → ∃ y ∈ S, y ∈ t }

def interior : set α :=
{ x | ∃ t ∈ X.is_open, x ∈ t ∧ t ⊆ S }

def frontier : set α :=
closure X S \ interior X S

def nbds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ is_open X s}, principal s)



-- skipping material on nets, do it with filters instead 
-- as in Isabelle, Coq, etc.

structure metric_space (α : Type u) : Type u :=
(dist : α → α → ℝ)
(non_negative : ∀ x y, 0 ≤ dist x y)
(dist0 : ∀ x y, dist x y = 0 → (x = y))
(dist_comm : ∀ x y, dist x y = dist y x)
(triangle_ineq : ∀ x y z, dist x z ≤ dist x y + dist y z)

attribute [class] metric_space

def open_ball (m: metric_space α) (x : α) (r : ℝ) : (set α) :=
{y : α | m.dist x y < r}



axiom submetric_exists :
Π {α : Type u} (m: metric_space α) (s: set α),
(∃! (X : metric_space (subtype s)), ∀ x y, X.dist x y = m.dist x y) 
-- { description := "a metric uniquely restricts to a metric on each subset" }

def submetric (m : metric_space α) (s : set α) : (metric_space (subtype s)) :=
classical.some (submetric_exists m s)

axiom mtopological_space_exists :
Π {α : Type u} (m : metric_space α),
(∃! (X : topological_space α), X.is_open = {u | ∀ x ∈ u, ∃ r > 0, open_ball m x r ⊆ u}) 
-- { description := "every metric determines a unique topological_space" }

def mtopological_space (m : metric_space α) : (topological_space α) :=
classical.some (mtopological_space_exists m)

instance : has_coe (metric_space α) (topological_space α) :=
⟨ mtopological_space ⟩

def closed_ball (m : metric_space α) (x : α) (r : ℝ) : (set α) :=
{y : α | m.dist x y ≤ r}

axiom discrete_metric_exists :
Π (α : Type u),
(∃! (X : metric_space α), ∀ x y, X.dist x y = if x=y then 0 else 1) 
-- { description := "the discrete metric is a metric" }

def discrete_metric (α : Type u) : (metric_space α) :=
classical.some (discrete_metric_exists α)

def sphere (m : metric_space α) (x : α) (r : ℝ) : (set α) :=
{y : α | m.dist x y = r}

def bounded (m : metric_space α) :=
(∃ x r, S ⊆ closed_ball m x r)

def compact_in :=
(∀ U, (∀ u ∈ U, is_open X u) ∧ (S ⊆ ⋃₀ U) → (∃ V, finite V ∧ V ⊆ U ∧ S ⊆ ⋃₀ V))

def compact_space :=
compact_in X univ

def connected_space :=
(¬(∃ e1 e2, is_open X e1 ∧ is_open X e2 ∧ e1 ∪ e2 = univ  ∧ e1 ∩ e2 = ∅ 
  ∧ ¬(e1 = ∅) ∧ ¬(e2 = ∅)))

def connected_in :=
connected_space (induced_space X S)

def neighbourhood_base_at (x : α) (P : set (set α)) (X : topological_space α) : Prop :=
(∀ w, is_open X w ∧ x ∈ w → ∃ u v, is_open X u ∧ v ∈ P ∧ x ∈ u ∧ u ⊆ v ∧ v ⊆ w) 

def neighbourhood_base_of (P : set(set α)) (X : topological_space α) : Prop :=
(∀ x, neighbourhood_base_at x P X)

def metrizable_space :=
(∃ m, X = mtopological_space m)

-- redo as classes extending top spaces?
-- T1 spaces
def t1_space :=
(∀ x y, ¬(x=y) → ∃ u, is_open X u ∧ x ∈ u ∧ ¬(y ∈ u))

def hausdorff_space :=
(∀ x y, ¬(x=y) → ∃ u v, is_open X u ∧ is_open X v ∧ x ∈ u ∧ x ∈ v ∧ disjoint u v)

def regular_space :=
(∀ c a, is_closed X c ∧ ¬(a ∈ c) → ∃ u v, is_open X u ∧ is_open X v ∧ a ∈ u ∧ c ⊆ v ∧ disjoint u v)

def locally_compact_space :=
(∀ x, ∃ u k, is_open X u ∧ compact_in X k ∧ x ∈ u ∧ u ⊆ k)

def normal_space :=
(∀ s t, is_closed X s ∧ is_closed X t ∧ disjoint s t →
(∃ u v, is_open X u ∧ is_open X v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v))

-- cauchy

variable (f : α → β)

def cauchy_in [m : metric_space α] (s : ℕ → α) :=
(∀ ε > 0, ∃ N, ∀ n n', N ≤ n ∧ N ≤ n' → m.dist (s n) (s n') < ε)

class complete_metric_space α [m : metric_space α] :=
(completeness : ∀ (s : ℕ → α), cauchy_in s → 
  ∃ (x : α), ∀ ε > 0, ∃ N, ∀ n, n ≥ N → m.dist x (s n) < ε)

def totally_bounded_in (m : metric_space α) :=
(∀ ε > 0, ∃ k, finite k ∧ k ⊆ S ∧ S ⊆ ⋃₀ { b | ∃ x ∈ k, b = open_ball m x ε })

def continuous_at (x : α) :=
(∀ v, is_open Y v ∧ f x ∈ v → ∃ u, is_open X u ∧ x ∈ u ∧ (∀ y ∈ u, f y ∈ v))

def continuous_map :=
(∀ u, is_open Y u → is_open X (preimage f u))

def open_map :=
(∀ u, is_open X u → is_open Y (image f u))

def closed_map :=
(∀ u, is_closed X u → is_closed Y (image f u))

def lipschitz_continuous_map (m1 : metric_space α) (m2 : metric_space β) (f : α → β) :=
(∃ b, ∀ x y, m2.dist (f x) (f y) ≤ b * m1.dist x y)

def uniformly_continuous_map (m1 : metric_space α) (m2 : metric_space β) (f : α → β) :=
(∀ e > 0, ∃ d > 0, ∀ x x', m1.dist x' x < d → m2.dist (f x') (f x) < e)

def cauchy_continuous_map (m1 : metric_space α) (m2 : metric_space β) (f : α → β) :=
(∀ x, @cauchy_in α m1 x → @cauchy_in β m2 (f ∘ x))


-- metric on ℝ
-- We have the usual need for a coercion ℝ to ℝ¹.

/-
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
(∃ m : metric_space ℝ, ∀ x y, m.dist x y = real_abs(x - y)) :=
{ description := "the Euclidean metric exists" }

def real_euclidean_metric1 : metric_space ℝ :=
classical.some real_euclidean_metric_exists

def real_bounded (s : set ℝ) : Prop :=
(∃ r, ∀ x ∈ s, real_abs(x) ≤ r)

def real_compact (s : set ℝ) : Prop :=
compact_in euclideanreal s
-/

-- Euclidean metric space

-- duplicates Kepler conjecture
local infix `^` := real.pow

-- duplicates Kepler conjecture
def real_euclidean_metric {n : ℕ} 
(u : vector ℝ n) (v : vector ℝ n) : ℝ :=
let subsquare (x : ℝ) (y : ℝ) : ℝ := (x-y)^2,
    sqs := to_list (map₂ subsquare u v) in real.sqrt (list.sum sqs)

variable {n : ℕ}

axiom real_euclidean_metric_exists :
(∃! m : metric_space (vector ℝ n), ∀ x y, m.dist x y = real_euclidean_metric x y)

instance : metric_space (vector ℝ n) :=
classical.some real_euclidean_metric_exists

-- issue #54: intersection of sig-algebras




def sigma_algebra_closure (A : set (set α)) :=
⋂₀ {σ : set (set α) | nonempty(sigma_algebra σ) ∧ A ⊆ σ}

axiom sigma_algebra_closure_is_sigma_algebra (A : set(set α)) :
nonempty (sigma_algebra (sigma_algebra_closure A))

def borel_algebra ( Y : topological_space α)  := 
choice (sigma_algebra_closure_is_sigma_algebra (Y.is_open))

def borel_algebra_Rn (n:ℕ) [Y : topological_space (vector ℝ n)] := 
borel_algebra Y

-- for ℝ

def is_realinterval (s : set ℝ) :=
(∀ a b c, a ∈ s ∧ b ∈ s ∧ a ≤ c ∧ c ≤ b → c ∈ s)

def open_real_interval a b :=
{ x : ℝ | a < x ∧ x < b }

def closed_real_interval a b :=
{ x : ℝ | a ≤ x ∧ x ≤  b }





end metric

