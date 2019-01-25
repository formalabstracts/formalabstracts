import data.nat.enat
import dvector

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- The Monster group -/

/- according to: https://mathoverflow.net/questions/142205/presentation-of-the-monster-group

There's a 12-generator 80-relator presentation for the Monster group. Specifically, we have 78 relators for the Coxeter group Y443:12 relators of the form x2=1
, one for each node in the Coxeter-Dynkin diagram;
11 relators of the form (xy)3=1, one for each pair of adjacent nodes; 55 relators of the form (xy)2=1 (commutators), one for each pair of non-adjacent nodes; together with a single 'spider' relator, (ab1c1ab2c2ab3c3)10=1 , which results in the group M×C2. We can get rid of the C2 by quotienting out by an eightieth relation, x=1, where x is the unique non-identity element in the centre of the group. -/ 

@[derive decidable_eq]inductive coxeter_vertices {n : ℕ} (xs : dvector ℕ n) : Type
| torso : coxeter_vertices
| arm : ∀ x : dfin n, dfin (xs.nth'' x + 1) → coxeter_vertices

open coxeter_vertices

inductive coxeter_edges_directed {n : ℕ} (xs : dvector ℕ n) : (coxeter_vertices xs) → (coxeter_vertices xs) → Prop 
| edge_torso : ∀ i : dfin n , coxeter_edges_directed (arm i dfin.fz) (torso _)
| edge_arm : ∀ i : dfin n, ∀ v : dfin (xs.nth'' i + 1), v ≠ dfin.last _ → coxeter_edges_directed (arm i v) (arm i (v+1)) 

inductive symmetric_closure {α : Type*} (E : α → α → Prop) : α → α → Prop
| incl : ∀ a b : α, E a b → symmetric_closure a b
| symm : ∀ a b : α, symmetric_closure a b → symmetric_closure b a

def coxeter_edges {n : ℕ} (xs : dvector ℕ n) : coxeter_vertices xs → coxeter_vertices xs → Prop
  := symmetric_closure (coxeter_edges_directed xs)

