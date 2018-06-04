/- 
Frechet derivatives on Banach space

-/

import order.filter data.set meta_data data.list data.vector
       .real_axiom algebra.module data.finset.basic .metric
       .complex

noncomputable theory

namespace derivatives

open set filter classical nat int list vector real_axiom metric finset complex

local attribute [instance] prop_decidable

universes u v w

-- could do normed rings, non-multiplicative norms,  as well.


-- variables { α :Type u} {β : Type v} ( x : α ) (y : β) [ring α] [topological_space α]
-- #check induced_space _ { x : α | x ≠ 0 }

-- #check product_topology

-- this must be somewhere already...

/-
def uncurry {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ ) (xy : α × β) :=
let (x,y) := xy in f x y

def curry {α : Type u} {β : Type v} {γ : Type w} (f : α × β → γ ) (x  : α) (y : β) := f (x,y)
-/

class topological_ring (α : Type u) [rngtop : topological_space α] extends ring α :=
(minus_cont : continuous_map product_topology rngtop (λxy, xy.fst - xy.snd))
(time_cont : continuous_map product_topology rngtop (λxy, xy.fst * xy.snd))

class topological_field (α : Type u) [field α] [top : topological_space α] extends topological_ring α  :=

(inv_cont : continuous_map (induced_space top { x : α | x ≠ 0 }) top (λx, x⁻¹))

variables {α : Type u} {β : Type v} (xy : α × β)
-- #check let (x,y) := xy in (x : α)

class multiplicative_normed_field (α : Type u) extends field α, metric_space α :=
(norm : α → ℝ)
(multiplicative : ∀ x y, norm(x*y) = norm x * norm y)
(norm_dist : ∀ x y, dist x y = norm (x - y))
--follows from metric
--(positivity : ∀ x, norm x ≥ 0)
--(norm0 : ∀ x, norm x = 0 ↔ x = 0)
--(triangle_inequality : ∀ x y, norm(x + y) ≤ norm x + norm y)



class topological_vector_space (α : Type u) (β : Type v) [field α] [X:topological_space β] extends vector_space α β :=
(closed_points : ∀ (x : β), is_closed X {x})




class normed_space (α : Type u) (β : Type v) [multiplicative_normed_field α] extends vector_space α β, metric_space β :=
(norm  : β → ℝ := λ (v:β), dist v 0 )
(homogeneity : ∀ (c : α) (v : β), norm(c  • v) = multiplicative_normed_field.norm c * norm v)
(norm_dist : ∀ v w, dist v w = norm (v - w))

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















end derivatives
