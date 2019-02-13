import .basic data.dvector data.nat.prime

noncomputable theory
universes u v

/- Dynkin diagrams -/

/- A Dynkin diagram is a graph where the edges are annotated with positive natural numbers. If an edge is annotated with 1, then it is undirected, otherwise directed -/
structure dynkin_diagram :=
  (vertex : Type v)
  (edge : vertex → vertex → Prop)
  (annotation : Π{{x y}}, edge x y → ℕ+)
  (directed : Π{{x y}} (e : edge x y), annotation e = 1 ↔ edge y x)

namespace dynkin_diagram

  /-- The undirected closure of a graph, which adds the symemtric edge whenever the annotation of an edge is equal to 1 -/
  def undirected_closure
    (vertex : Type v)
    (edge : vertex → vertex → Prop)
    (annotation : Π{{x y}}, edge x y → ℕ+)
    (directed : Π{{x y}} (v : edge x y), edge y x → annotation v = 1) : dynkin_diagram :=
  ⟨vertex, λ v w, edge v w ∨ ∃(e : edge w v), annotation e = 1,
    λ x y e,
    have h : ∃(n : ℕ+), (edge y x → n = 1) ∧ ∀(e : edge x y), n = annotation e, from omitted,
    classical.some h, omitted⟩

  /- The following are all Dynkin diagrams of simple root systems -/

  /-- The edges of the Dynkin diagrams A_n and B_n -/
  inductive A_edges {n : ℕ+} : dfin n → dfin n → Prop
  | mk : Π(x : dfin n), x.to_nat + 1 ≠ n → A_edges x (x+1)

  /-- The Dynkin diagram $A_n$ -/
  protected def A (n : ℕ+) : dynkin_diagram :=
  undirected_closure (dfin n) A_edges (λ x y e, 1) (λ x y e e', rfl)

  /-- The Dynkin diagram $B_n$ -/
  protected def B (n : ℕ+) : dynkin_diagram :=
  undirected_closure (dfin n) A_edges (λ x y e, if y.to_nat+1 = ↑n then 2 else 1) omitted

  /-- The edges of the Dynkin diagrams C_n -/
  inductive C_edges {n : ℕ+} : dfin n → dfin n → Prop
  | mk : Π(x : dfin n), x.to_nat + 1 ≠ n → C_edges (x+1) x

  /-- The Dynkin diagram $C_n$ -/
  protected def C (n : ℕ+) : dynkin_diagram :=
  undirected_closure (dfin n) C_edges (λ x y e, if x.to_nat+1 = n then 2 else 1) omitted

/-- The edges of the Dynkin diagrams D_n -/
  inductive D_edges {n : ℕ+} : dfin n → dfin n → Prop
  | mk : Π(x : dfin n), x.to_nat ≠ 0 → x.to_nat + 1 ≠ n → D_edges x (x+1)
  | extra : D_edges 0 2

  /-- The Dynkin diagram $D_n$ -/
  protected def D (n : ℕ+) : dynkin_diagram :=
  undirected_closure (dfin n) D_edges (λ x y e, 1) (λ x y e e', rfl)

  inductive E_edges {n : ℕ+} : dfin n → dfin n → Prop
  | mk : Π(x : dfin n), x.to_nat ≠ 0 → x.to_nat + 1 ≠ n → E_edges x (x+1)
  | extra : E_edges 0 3

  /-- The Dynkin diagram $E_n$ (for n ≥ 2) -/
  protected def E (n : ℕ+) : dynkin_diagram :=
  undirected_closure (dfin n) E_edges (λ x y e, 1) (λ x y e e', rfl)

  /-- The Dynkin diagram $F_4$ -/
  protected def F4 : dynkin_diagram :=
  undirected_closure (dfin (4 : ℕ+)) A_edges (λ x y e, if x = 1 then 2 else 1) omitted

  /-- The Dynkin diagram $G_2$ -/
  protected def G2 : dynkin_diagram :=
  undirected_closure (dfin (2 : ℕ+)) A_edges (λ x y e, 3) omitted

  /-- The set of all isomorphisms between two dynkin diagrams is defined as the graph isomorphisms which ignore the direction of directed edges but preserve the annotation. -/
def dynkin_diagram_isomorphism (X Y : dynkin_diagram) :=
{f : X.vertex ≃ Y.vertex |
  ∀(x x' : X.vertex), (X.edge x x' ↔ Y.edge (f x) (f x') ∨ Y.edge (f x') (f x)) ∧
  ∀(e : X.edge x x'), (∀(e' : Y.edge (f x) (f x')), X.annotation e = Y.annotation e') ∧
                      (∀(e' : Y.edge (f x') (f x)), X.annotation e = Y.annotation e') }

local infix ` ≅ ` := dynkin_diagram_isomorphism

local attribute [instance, priority 0] classical.prop_decidable

/-- If f reverses the direction of an arrow, returns `some n` where `n` is the annotation of that edge (chooses the smallest n in case of a tie), and otherwise returns `none`. -/
def reverses_an_arrow {X Y : dynkin_diagram} (f : X ≅ Y) : option ℕ :=
if h : ∃(x x' : X.vertex) (e : X.edge x x'), ¬Y.edge (f x) (f x')
then
have h' : ∃(n : ℕ) (x x' : X.vertex) (e : X.edge x x'), ¬Y.edge (f x) (f x') ∧
  ↑(X.annotation e) = n,
from let ⟨x, x', e, he⟩ := h in ⟨X.annotation e, x, x', e, he, rfl⟩,
some $ nat.find h'
else none

/-- A finite simple group of Lie type is a triple `(X,ρ,q)` where `X` is a Dynkin diagram of simple root system, `ρ` is an automorphism of the diagram and `q = p^e` where `p` is a prime and `e ∈ ½ℤ` such that
* If `ρ` flips the direction of an arrow with annotation `p'`, then `p = p'`
* Otherwise, `e ∈ ℤ` -/
/- We store `2e` instead of `e` -/
structure finite_simple_group_of_lie_type :=
  (X : dynkin_diagram)
  (ρ : X ≅ X)
  (p : ℕ)
  (two_e : ℤ)
  (p_prime : p.prime)
  (h_flip : ∀n, reverses_an_arrow ρ = some n → n = p)
  (h_noflip : reverses_an_arrow ρ = none → ∃e' : ℤ, two_e = e')

end dynkin_diagram


def chevalley_group (G : Group) : Prop :=
sorry

def steinberg_group (G : Group) : Prop :=
sorry

def ree_group (G : Group) : Prop :=
sorry

def suzuki_group (G : Group) : Prop :=
sorry

def tits_group (G : Group) : Prop :=
sorry
