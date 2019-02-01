import topology.instances.real data.pfun2 order.lattice ...basic
open topological_space set

noncomputable theory
universes u v w

variables {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

/- continuity of a partial function -/
namespace pfun
def is_continuous [topological_space α] [topological_space β] (f : α →. β) := 
continuous (f.as_subtype)

def is_continuous_id [topological_space α] : is_continuous (@pfun.id α) := omitted
end pfun

open pfun
-- instance [t : topological_space α] : topological_space (vector α n) :=
-- ⨆(l : fin n), induced (λ x, vector.nth x l) t

structure Top :=
  (carrier : Type u)
  (struct : topological_space carrier)

namespace Top

instance : has_coe_to_sort Top := ⟨Type*, Top.carrier⟩
attribute [instance] Top.struct

def restrict (X : Top) (s : set X) : Top := ⟨subtype s, by apply_instance⟩

end Top

structure euclidean_space :=
(carrier : Type u)
(dim : ℕ)
(equiv : carrier ≃ vector ℝ dim)

namespace euclidean_space
instance : has_coe_to_sort euclidean_space := ⟨Type*, euclidean_space.carrier⟩

instance to_topological_space (E : euclidean_space) : 
  topological_space E :=
induced (@euclidean_space.equiv E) (by apply_instance)

def to_Top (E : euclidean_space) : Top :=
⟨E, by apply_instance⟩

instance : has_coe euclidean_space Top :=
⟨to_Top⟩

def real_euclidean_space (n : ℕ) : euclidean_space :=
⟨ℝ, 1, vector.vector_one_equiv.symm⟩

def standard_euclidean_space (n : ℕ) : euclidean_space :=
⟨vector ℝ n, n, equiv.refl _⟩

notation `ℝ^` := standard_euclidean_space
end euclidean_space

variables {k k' : ℕ∞} {E : euclidean_space.{u}} {E' : euclidean_space.{v}}
def is_smooth_at (k : ℕ∞) (f : E →. E') (x : E) : Prop := sorry
def is_smooth (k : ℕ∞) (f : E →. E') : Prop := sorry --∀x, is_smooth_at k f x

/- the empty map is smooth -/
lemma is_smooth_empty (k : ℕ∞) (E E' : euclidean_space) : is_smooth k (pfun.empty E E') := omitted

/- every smooth map is continuous -/
lemma is_continuous_of_is_smooth {f : E →. E'} (hf : is_smooth k f) : f.is_continuous := 
omitted

lemma is_smooth_of_le {f : E →. E'} (hf : is_smooth k f) (hk : k' ≤ k) : is_smooth k' f := 
omitted

/- a partial homeomorphism -/
structure phomeo (X Y : Top) extends X ≃. Y :=
(continuous_to_fun  : to_fun.is_continuous)
(continuous_inv_fun : inv_fun.is_continuous)

infixr ` ≃ₜ. `:25 := phomeo

namespace phomeo
variables {X : Top} {Y : Top} {Z : Top}
def restrict_phomeo (p : set X) : X.restrict p ≃ₜ. X :=
⟨pequiv.subtype_pequiv p, omitted, omitted⟩

protected def rfl : X ≃ₜ. X := ⟨pequiv.rfl, is_continuous_id, is_continuous_id⟩
protected def refl (X) : X ≃ₜ. X := phomeo.rfl
def symm (f : X ≃ₜ. Y) : Y ≃ₜ. X := ⟨f.to_pequiv.symm, f.continuous_inv_fun, f.continuous_to_fun⟩
def trans (f : X ≃ₜ. Y) (g : Y ≃ₜ. Z) : X ≃ₜ. Z := ⟨f.to_pequiv.trans g.to_pequiv, omitted, omitted⟩

end phomeo