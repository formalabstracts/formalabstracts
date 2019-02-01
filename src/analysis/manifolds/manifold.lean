import .basic
open pfun topological_space set
noncomputable theory
universes u v w

variables {k : ℕ∞} {E : euclidean_space.{u}}

/- topological manifolds -/
structure chart (X : Top) (E : euclidean_space) :=
  (iso : X ≃ₜ. E.to_Top)
  (h1 : is_open iso.to_fun.dom)
  (h2 : is_open iso.inv_fun.dom)

namespace chart
variable {X : Top}
def to_fun (c : chart X E) : X →. E := c.iso.to_fun
def inv_fun (c : chart X E) : E →. X := c.iso.inv_fun
def domain (c : chart X E) : set X := dom c.to_fun
def codomain (c : chart X E) : set E := dom c.inv_fun

def restrict {s : set X} (hs : is_open s) (c : chart X E) : chart (X.restrict s) E :=
⟨(phomeo.restrict_phomeo s).trans c.iso, omitted, omitted⟩

end chart

def compatible_charts {X : Top} (k : ℕ∞) (c₁ c₂ : chart X E) : Prop :=
is_smooth k (c₂.to_fun ∘. c₁.inv_fun) ∧ 
is_smooth k (c₁.to_fun ∘. c₂.inv_fun)

structure topological_manifold (E : euclidean_space) :=
  (carrier : Top)
  (struct2 : t2_space carrier)
  (struct3 : second_countable_topology carrier)
  (charts : set (chart carrier E))
  (cover : ⋃₀ (chart.domain '' charts) = univ)

namespace topological_manifold
instance : has_coe (topological_manifold E) Top :=
⟨topological_manifold.carrier⟩

def restrict (X : topological_manifold E) {s : set X} (hs : is_open s) : 
  topological_manifold E :=
⟨X.carrier.restrict s, omitted, omitted, chart.restrict hs '' X.charts, omitted⟩ 

end topological_manifold

structure differentiable_manifold (k : ℕ∞) (E : euclidean_space) extends topological_manifold E :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → compatible_charts k c₁ c₂)

namespace euclidean_space

  def to_differentiable_manifold (E : euclidean_space) (k : ℕ∞) : differentiable_manifold k E :=
  ⟨⟨E.to_Top, omitted, omitted, {⟨phomeo.rfl, is_open_univ, is_open_univ⟩}, omitted⟩, omitted⟩

end euclidean_space

namespace differentiable_manifold

instance : has_coe (differentiable_manifold k E) Top :=
⟨λX, X.to_topological_manifold.carrier⟩

/- a maximal atlas is a set of charts which is compatible with all charts of X -/
def max_atlas (X : differentiable_manifold k E) : set (chart X.carrier E) :=
{ c | ∀c' ∈ X.charts, compatible_charts k c c' }

/- examples and constructions -/
def restrict (X : differentiable_manifold k E) {s : set X} (hs : is_open s) : 
  differentiable_manifold k E :=
⟨X.to_topological_manifold.restrict hs, omitted⟩ 


def sphere (n : ℕ) : differentiable_manifold ⊤ (euclidean_space.standard_euclidean_space n) :=
sorry --⟨⟨⟨subtype _, _⟩, _, _, _, _⟩, omitted⟩

/- smooth maps-/
variables {X : differentiable_manifold k E} {Y : differentiable_manifold k E} {Z : differentiable_manifold k E}

def respects_charts (f : X → Y) (A : set (chart X.carrier E)) (B : set (chart Y.carrier E)) : Prop := 
∀(c ∈ A) (c' ∈ B), is_smooth k (chart.to_fun c' ∘. pfun.lift f ∘. chart.inv_fun c)

structure smooth_map (X Y : differentiable_manifold k E) :=
  (map : X → Y)
  (smooth : respects_charts map X.max_atlas Y.max_atlas)

infix ` →ₛ `:25 := smooth_map

def incl (X : differentiable_manifold k E) {s : set X} (hs : is_open s) :
  restrict X hs →ₛ X :=
⟨subtype.val, omitted⟩

lemma respects_charts_local (f : X → Y) (A : set (chart X.carrier E)) (B : set (chart Y.carrier E))
  (h : ∀x : X, ∃(s : set X) (hs : is_open s), x ∈ s ∧ 
    respects_charts (f ∘ (incl X hs).map) (chart.restrict hs '' A) B) : respects_charts f A B :=
omitted

lemma respects_charts_subset (f : X → Y) (A A' : set (chart X.carrier E)) (B B' : set (chart Y.carrier E))
  (hA : ⋃₀ (chart.domain '' A') ⊆ ⋃₀ (chart.domain '' A)) (hB : ⋃₀ (chart.domain '' B') ⊆ ⋃₀ (chart.domain '' B))
  (h : respects_charts f A B) : respects_charts f A' B' :=
omitted

namespace smooth_map

def id : X →ₛ X := ⟨id, omitted⟩
def comp (g : Y →ₛ Z) (f : X →ₛ Y) : X →ₛ Z := ⟨g.map ∘ f.map, omitted⟩

end smooth_map



end differentiable_manifold
