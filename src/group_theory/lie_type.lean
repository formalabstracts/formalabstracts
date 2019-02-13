import .basic data.dvector

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
