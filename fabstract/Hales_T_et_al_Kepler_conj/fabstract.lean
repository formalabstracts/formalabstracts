import ...meta_data ...folklore.real_axiom
import data.list data.vector 

namespace Hales_T_et_al_Kepler_conj

noncomputable theory

open classical nat set list vector real_axiom

-- cardinality of finite sets. 
-- Surely this must exist somewhere. But where?
universe u

def set_of_list {α : Type u} : (list α) → set α
| [] y := false
| (x :: rest) y := (x = y) ∨ set_of_list rest y

def finite {α : Type u} (P : set α) :=
(∃ l, P = set_of_list l)

constant least (P : set ℕ) : ℕ

axiom least_empty : (least ∅ = 0) 

axiom least_nonempty (P : set ℕ) : 
(P ≠ ∅ → (least P ∈ P ∧ ∀ m, m ∈ P → least P ≤ m))

-- defaults to zero if the set is not finite:
def card {α : Type u} (P : set α) : ℕ :=
least (λ n, ∃ xs, set_of_list xs = P ∧ list.length xs = n)

/-
 Here are some Euclidean vector space definitions that
 should eventually be part of a general library
-/
local infix `^` := real_pow

def euclid_metric {n : ℕ} (u : vector ℝ n) (v : vector ℝ n) : ℝ :=
let subsquare (x : ℝ) (y : ℝ) : ℝ := (x-y)^2,
    d := to_list (map₂ subsquare u v) in real_sqrt (list.sum d)

def packing {n : ℕ} (V : set (vector ℝ n)) := 
(∀ u v, V u ∧ v ∈ V ∧ euclid_metric u v < 2 → (u = v))

-- Todo: check that open balls are used (not that it matters)
def open_ball {n : ℕ} (x0 : vector ℝ n) (r : ℝ) : (set (vector ℝ n)) :=
{ u | euclid_metric x0 u < r}

def origin₃ : vector ℝ 3 := [0,0,0]

axiom Kepler_conjecture :
(∀ (V : set (vector ℝ 3)), packing V → 
  (∃ (c : ℝ), ∀ (r : ℝ), (r ≥ 1) -> 
  (↑(card(V ∩ open_ball origin₃ r)) ≤ pi* r^3/real_sqrt(18) + c*r^2)))

open result

def fabstract : meta_data := {
  description := "This article announces the formal proof of the Kepler conjecture on dense sphere packings in a combination of the HOL Light and Isabelle/HOL proof assistants.  It represents the primary result of the now completed Flyspeck project.",
  authors := ["Thomas Hales", "Mark Adams", "Gertrud Bauer", "Tat Dat Dang", "John Harrison", "Le Truong Hoang", "Cezary Kaliszyk", "Victor Magron", "Sean McLaughlin", "Tat Thang Nguyen", "Quang Truong Nguyen", "Tobias Nipkow", "Steven Obua", "Joseph Pleso", "Jason Rute", "Alexey Solovyev", "Thi Hoai An Ta", "Nam Trung Tran", "Thi Diep Trieu", "Josef Urban", "Ky Vu", "Roland Zumkeller"],
  primary := cite.DOI "/10.1017/fmp.2017.1",
  secondary := [],
  results := [Proof Kepler_conjecture]
}

end Hales_T_et_al_Kepler_conj
