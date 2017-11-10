/- 
Frechet derivatives on Banach space
-/

import --order.filter data.set meta_data data.list data.vector
       --topology.metric_space
       --algebra.module --data.finset.basic  -- .metric
       .banach

noncomputable theory

open set filter classical

local attribute [instance] prop_decidable

universes u v w

namespace axiomatic

class module.morphism (α : Type u) (β : Type v) (γ : Type w) [ring α] [module α β] [module α γ] :=
(f : β → γ)
(has_scalar : ∀ (x : α) (v : β), f (x • v) = x • f v)
(additive : ∀ (v w : β), f (v + w) = f v + f w)

instance 
(α : Type u) (β : Type v) (γ : Type w) [ring α] [module α β] [module α γ] : 
has_coe_to_fun (module.morphism α β γ) := { F := λ h, β → γ , coe := λ h, h.f }

variables (α : Type u) (β : Type v) (γ : Type w) [ring α] [module α β] [module α γ]

variables [comm_ring α]

class module.morphism.axioms (α : Type u) (β : Type v) (γ : Type w) [ring α] [module α β] [module α γ] :=
(carrier : module α (module.morphism α β γ))
(zero :  ∀  (x : β), (0 : module.morphism α β γ) x = (0 : γ))
(add : ∀ (L₁ L₂ : module.morphism α β γ), ∀ (x : β), (L₁ + L₂) x  = L₁ x + L₂ x)
(scalar : ∀ (L : module.morphism α β γ), ∀ (r : α), ∀ (x : β), (r • L) (x) = r • (L x))
(neg : ∀ (L : module.morphism α β γ),  ∀ (x : β), (- L) (x) = - (L x))

constant module.morphism.axioms_c : module.morphism.axioms α β γ  ---module α (module.morphism α β γ)
/-
attribute [instance] module.morphism.axioms_c --  : 
def module_structure : module α (module.morphism α β γ) := module.morphism.axioms.carrier α β γ 
attribute [instance] module_structure
-/



/-
--specified such that
axiom module.morphism.zero :  ∀  (x : β), (0 : module.morphism α β γ) x = (0 : γ)

axiom module.morphism.add : ∀ (L₁ L₂ : module.morphism α β γ), ∀ (x : β), 
(L₁ + L₂) x  = L₁ x + L₂ x

axiom module.morphism.scalar : ∀ (L : module.morphism α β γ), ∀ (r : α), ∀ (x : β), 
(r • L) (x) = r • (L x)

axiom module.morphism.neg : ∀ (L : module.morphism α β γ),  ∀ (x : β), 
(- L) (x) = - (L x)
-/

--#check module.mk
--#check has_scalar.mk
--#check add_comm_group.mk


/-
--axiom module.morphism.zero : (∃! (zero : module.morphism α β γ), ∀ (x : β), module.morphism.f α γ x = 0)
--instance : has_zero (module.morphism α β γ) := ⟨ classical.some (module.morphism.zero α β γ) ⟩
--variables {α β γ}

axiom module.morphism.add : 
(∃! (add : module.morphism α β γ → module.morphism α β γ → module.morphism α β γ), 
∀ (L₁ L₂ : module.morphism α β γ), ∀ (x : β), (add L₁ L₂) x  = L₁ x + L₂ x)

instance 
(α : Type u) (β : Type v) (γ : Type w) [ring α] [module α β] [module α γ] : 
has_add (module.morphism α β γ) := ⟨ classical.some (module.morphism.add α β γ) ⟩

axiom module.morphism.scalar 
(β : Type v) (γ : Type w) [module α β] [module α γ]  : 
(∃! (op : α → module.morphism α β γ → module.morphism α β γ), 
 ∀ (r : α) (φ : module.morphism α β γ) (x : β), (op r φ) x = φ (r • x))

instance (β : Type v) (γ : Type w) [module α β] [module α γ] :
has_scalar α (module.morphism α β γ) := 
⟨ classical.some (module.morphism.scalar α β γ) ⟩


axiom module.morphism.neg
(β : Type v) (γ : Type w) [module α β] [module α γ]  : 
(∃! (neg : module.morphism α β γ → module.morphism α β γ), 
 ∀ (φ : module.morphism α β γ) (x : β), (neg φ) x = - φ x)

instance (β : Type v) (γ : Type w) [module α β] [module α γ] :
has_neg (module.morphism α β γ) := 
⟨ classical.some (module.morphism.neg α β γ) ⟩
-/


end axiomatic

instance real.has_norm : has_norm ℝ := ⟨ real.abs ⟩ 

axiom real.normed_ring : normed_ring ℝ
attribute [instance] real.normed_ring

def scale_set {β : Type v} [module ℝ β] (t : ℝ) (U : set β) :=
{ x | ∃ u ∈ U, x = t • u }

reserve infix ` ◆ `:100 -- di
local infix ◆ := scale_set


section

variables {β : Type v} [topological_space β] [t1_space β] [vector_space ℝ β]

class bounded [t1_topological_vector_space ℝ β] (E : set β) : Prop :=
(bounded : ∀ (U : set β), is_open U → ∃ (s > 0), ∀ (t : ℝ), t > s → E ⊆ t ◆ U)

end

section

variables (β : Type v) 

variables [vector_space ℝ β] [metric_space β] [t1_topological_vector_space ℝ β] [has_norm β] [complete_space β]
class real_banach_space extends banach_space ℝ β

end

namespace axiomatic

variables (β : Type v) (γ : Type w)
variables [vector_space ℝ β] [topological_space β] [t1_space β] [t1_topological_vector_space ℝ β] [has_norm β]
variables [vector_space ℝ γ] [topological_space γ] [t1_space γ] [t1_topological_vector_space ℝ γ] [has_norm γ]

class bounded_linear_operators := 
(L : module.morphism ℝ β γ)
(is_bounded : (∀ (E : set β), bounded E → bounded (L '' E)))

-- exists by continuity of addition:
constant module.bounded_linear_operators.module : module ℝ (bounded_linear_operators β γ)
attribute [instance] module.bounded_linear_operators.module

instance bounded_linear_operators.coe_to_fun :
has_coe_to_fun (bounded_linear_operators β γ) := { F := λ h, β → γ , coe := λ h, h.L }

--specified such that
axiom bounded_linear_operators.zero :  ∀  (x : β), (0 : bounded_linear_operators β γ) x = (0 : γ)

axiom bounded_linear_operators.add : ∀ (L₁ L₂ : bounded_linear_operators β γ), ∀ (x : β), 
(L₁ + L₂) x  = L₁ x + L₂ x

axiom bounded_linear_operators.scalar : ∀ (L : bounded_linear_operators β γ), ∀ (r : ℝ), ∀ (x : β), 
(r • L) (x) = r • (L x)

axiom bounded_linear_operators.neg : ∀ (L : bounded_linear_operators β γ),  ∀ (x : β), 
(- L) (x) = - (L x)

variables (L :bounded_linear_operators β γ)
variable (x : β)
#check L x -- ⇑L x : γ (lean-checker)

--temp XX
#print bounded_linear_operators.L
#print module.morphism.f --α β γ

-- def bounded_linear_operators.test (u : bounded_linear_operators β γ)   := 
-- @module.morphism.f ℝ _ (bounded_linear_operators.L β γ )



end axiomatic

namespace axiomatic
open metric_space

variables {β : Type v} [vector_space ℝ β] [metric_space β] [t1_topological_vector_space ℝ β] [has_norm β] [complete_space β] [real_banach_space β]
variables {γ : Type w} [vector_space ℝ γ] [metric_space γ] [t1_topological_vector_space ℝ γ] [has_norm γ] [complete_space γ] [real_banach_space γ]


#check has_norm.mk
#print instances has_coe_to_fun

variable (L : bounded_linear_operators β γ)

def r [topological_space β] [t1_space β] := 0
#check r -- r : ℕ 

#print axiomatic.bounded_linear_operators.coe_to_fun
--#print instances has_coe_to_fun

-- #check (⇑ L )

def bounded_linear_operators.norm : has_norm (bounded_linear_operators β γ) :=
⟨ λ (L : bounded_linear_operators β γ), 
  sup { y | ∃ (x : β), has_norm.norm x ≤ 1 ∧ has_norm.norm( (L.L.f : β → γ) x) = y }  ⟩

constant banach.bounded_linear_operators : real_banach_space (bounded_linear_operators β γ)

--- continue.

end axiomatic















