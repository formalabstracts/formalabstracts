/-
Convexity and polytopes following HOL Light
generalized to a general vector space over ℝ
-/

import order.filter data.set meta_data data.list data.vector
       .real_axiom algebra.module data.finset.basic .metric


noncomputable theory

namespace polytope

open set filter classical nat int list vector real_axiom metric finset

local attribute [instance] prop_decidable

universes u v w

variables {α : Type u} { β : Type u}

variable [vector_space ℝ β]

def hull (A : set (set α))  s :=
⋂₀ { t | A t ∧ s ⊆ t}

def affine (s : set β) :=
(∀ x y (u : ℝ) v, x ∈ s ∧ y ∈ s ∧ u + v = 1 → (u • x + v • y ∈ s))

def convex (s : set β) :=
(∀ x y (u : ℝ) v, x ∈ s ∧ y ∈ s ∧ 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 →
(u • x + v • y) ∈ s)

def conic (s : set β) :=
(∀ x (c : ℝ), x ∈ s ∧ 0 ≤ c → c • x ∈ s)

def affine_dependent (s : set β) :=
(∃ x ∈ s, x ∈ hull affine (s \ {x}))

def coplanar (s : set β) :=
(∃ u v w, s ⊆ hull affine {u,v,w})

def convex_on (f : β → ℝ) (s : set β) :=
(∀ x y u v, x ∈ s ∧ y ∈ s ∧ 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 →
f (u • x + v • y) ≤ u * f x + v * f y)

instance  : has_coe (finset β) (set β) :=
⟨ λ s, { x | x ∈ s} ⟩

open finset

def has_aff_dim (s : set β) (d : int) :=
(∃ (b : finset β), hull affine ( b :set β) = hull affine s ∧
 ¬ (affine_dependent (b : set β)) ∧ (card b : ℤ) = d +1)

def aff_dim_exists (s : set β) : Prop := (∃ d, has_aff_dim s d)

def aff_dim (s : set β) := if p : aff_dim_exists s then 
classical.some p else 0

def convex_cone (s : set β) :=
¬ (s= ∅) ∧ convex s ∧ conic s

def closed_segment (a : β) (b : β) :=
image (λ u, (1 - u) • a + u • b) { u | 0 ≤ u ∧ u ≤ 1}

def open_segment (a : β) (b : β) :=
closed_segment a b \ {a,b}



def starlike (s : set β) :=
(∃ a ∈ s, ∀ x ∈ s, closed_segment a x ⊆ s)

section

variables [X : topological_space β] 

def relative_interior (s : set β) :=
{ x : β | 
  ∃ t, is_open (induced_space X ((hull affine s) : set β)) t ∧
  x ∈ (t : set β) ∧ (t : set β) ⊆ s }

def relative_frontier (s : set β) :=
 closure X s \ relative_interior s

end -- section

def face_of t (s : set β) :=
(t ⊆ s ∧ convex t ∧ 
  (∀ a b x, a ∈ s ∧ b ∈ s ∧ x ∈ t ∧ x ∈ open_segment a b →
   a ∈ t ∧ b ∈ t))

/- -- skip needs dot product
def exposed_face_of t (s : set β) :=
(face_of t s ∧ ∃ a b, s ⊆ 
-/


/- -- skip need to find sum
def barycentre (s : finset β) :=
sum (λ (x : β), ((card s : ℝ)⁻¹ • x : β))
-/

def extreme_point_of (s : set β) x :=
(x ∈ s ∧ ∀ a b, a ∈ s ∧ b ∈ s → ¬(x ∈ open_segment a b))

def facet_of f (s : set β) :=
face_of f s ∧ ¬ ( f = ∅) ∧ aff_dim f = aff_dim s - 1

def edge_of e (s : set β) :=
face_of e s ∧ aff_dim e = 1

def polytope (s : set β) :=
(∃ (v : finset β), s = hull convex (v : set β))

-- skip polyhedron, uses dot

def simplex (n : int) (s : set β) :=
(∃ (c : finset β), ¬(affine_dependent (c : set β)) ∧
   (card c : int) = n + 1 ∧ s = hull convex (c : set β))

def simplicial_complex (c : finset (set β)) :=
(∀ s ∈ c, ∃ n, simplex n s) ∧
(∀ f s ∈ c, face_of f s → f ∈ c) ∧ 
(∀ s ∈ c, ∀ s' ∈ c, face_of (s ∩ s') s ∧ face_of (s ∩ s') s')

-- skip triangulation, uses ℝ^n


end polytope
