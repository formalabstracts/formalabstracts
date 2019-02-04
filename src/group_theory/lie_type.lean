import .basic

noncomputable theory
universes u v

/- Dynkin diagrams -/

/-- unordered pairs of distinct element-/
def upair (α : Type u) : Type u := {s : finset α // s.card = 2}

/-- given a function on ordered pairs which is independent of the ordering, we can construct a function on unordered pairs -/
-- TODO: redefine this so that it becomes computable
noncomputable def upair.elim {α β : Type*} (f : α → α → β) (h : Πx y, f x y = f y x) :
  upair α → β :=
λx, (λ (l : list α), f (l.nth_le 0 omitted) (l.nth_le 1 omitted)) x.1.1.out

-- structure annotated_graph (α : Type u) :=
--   (vertex : Type v)
--   (edge : vertex → vertex → Prop)
--   (annotation : Π{{xy}}, edge xy → α)

-- namespace annotated_graph 

--   variable {α : Type u}
--   def of_graph (V : Type v) (E : V → V → Prop) (A : Π{{v w}}, E v w → α) : annotated_graph α :=
--   ⟨V, upair.elim (λ v w, E v w ∨ E w v) omitted, _⟩

-- end annotated_graph

/- A Dynkin diagram is a graph where the edges are annotated with positive natural numbers. If an edge is annotated with 1, then it is undirected, otherwise directed -/
structure dynkin_diagram :=
  (vertex : Type v)
  (edge : vertex → vertex → Prop)
  (annotation : Π{{x y}}, edge x y → ℕ+)
  (directed : Π{{x y}} (e : edge x y), annotation e = 1 ↔ edge y x)

namespace dynkin_diagram 
  
  def undirected_closure 
    (vertex : Type v)
    (edge : vertex → vertex → Prop)
    (annotation : Π{{x y}}, edge x y → ℕ+) 
    (directed : Π{{x y}} (v : edge x y), edge y x → annotation v = 1) : dynkin_diagram :=
  ⟨vertex, λ v w, edge v w ∨ ∃(e : edge w v), annotation e = 1, 
    λ x y e, 
    have h : ∃(n : ℕ+), (edge y x → n = 1) ∧ ∀(e : edge x y), n = annotation e, from omitted,
    classical.some h, omitted⟩

  inductive A_edges {n : ℕ} : fin (n+1) → fin (n+1) → Prop
  | mk : Π(x : fin n), A_edges x (fin.cast_succ x)

  /-- The Dynkin diagram $A_{n+1}$ -/
  protected def A (n : ℕ) : dynkin_diagram :=
  undirected_closure (fin (n+1)) A_edges (λ x y e, 1) (λ x y e e', rfl)

  /-- The Dynkin diagram $B_{n+1}$ -/
  protected def B (n : ℕ) : dynkin_diagram :=
  undirected_closure (fin (n+1)) A_edges (λ x y e, if y = n then 2 else 1) omitted

  inductive C_edges {n : ℕ} : fin (n+1) → fin (n+1) → Prop
  | mk : Π(x : fin n), C_edges (fin.cast_succ x) x

  /-- The Dynkin diagram $C_{n+1}$ -/
  protected def C (n : ℕ) : dynkin_diagram :=
  undirected_closure (fin (n+1)) C_edges (λ x y e, if x = n then 2 else 1) omitted

  inductive D_edges {n : ℕ} : option (fin (n+1)) → option (fin (n+1)) → Prop
  | mk : Π(x : fin n), D_edges (some x) (some $ fin.cast_succ x)
  | extra : D_edges none (some 1)

  /-- The Dynkin diagram $D_{n+2}$ -/
  protected def D (n : ℕ) : dynkin_diagram :=
  undirected_closure (option (fin (n+1))) D_edges (λ x y e, 1) (λ x y e e', rfl)

  inductive E_edges {n : ℕ} : option (fin (n+1)) → option (fin (n+1)) → Prop
  | mk : Π(x : fin n), E_edges (some x) (some $ fin.cast_succ x)
  | extra : E_edges none (some 2)

  /-- The Dynkin diagram $E_{n+2}$ (for n ≥ 2) -/
  protected def E (n : ℕ) : dynkin_diagram :=
  undirected_closure (option (fin (n+2))) D_edges (λ x y e, 1) (λ x y e e', rfl)

  /-- The Dynkin diagram $F_4$ -/
  protected def F4 : dynkin_diagram :=
  undirected_closure (fin 4) A_edges (λ x y e, if x = 1 then 2 else 1) omitted

  /-- The Dynkin diagram $G_2$ -/
  protected def G2 : dynkin_diagram :=
  undirected_closure (fin 2) A_edges (λ x y e, 3) omitted

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
