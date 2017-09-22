import meta_data
       ...folklore.real_axiom
       data.vector

namespace Hales_T_et_al_Kepler_conj

noncomputable theory

open classical nat set list real_axiom vector

-- cardinality of finite sets.
-- Surely this must exist somewhere. But where?
universe u

def set_of_list {α : Type u} : (list α) → set α
| [] y := false
| (x :: rest) y := (x = y) ∨ set_of_list rest y

def finite {α : Type u} (P : set α) :=
(∃ l, P = set_of_list l)

unfinished least : set ℕ → ℕ :=
{ description := "every subset of natural numbers has a least element" }

unfinished least_empty : least ∅ = 0 :=
{ description := "the least element of the empty set is 0 by convention" }

unfinished least_nonempty :
  ∀ (P : set ℕ),
    P ≠ ∅ → (least P ∈ P ∧ ∀ m, m ∈ P → least P ≤ m) :=
{ description := "the defining property of the least element of a subset" }

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

-- this is a temporary workaround (https://github.com/leanprover/lean/commit/16e7976b1a7e2ce9624ad2df363c007b70d70096)
def origin₃ : vector ℝ 3 := 0::0::0::nil--[0,0,0]

def hales_et_al_paper : document :=
{ authors := [
    {name := "Thomas Hales"},
    {name := "Mark Adams"},
    {name := "Gertrud Bauer"},
    {name := "Tat Dat Dang"},
    {name := "John Harrison"},
    {name := "Le Truong Hoang"},
    {name := "Cezary Kaliszyk"},
    {name := "Victor Magron"},
    {name := "Sean McLaughlin"},
    {name := "Tat Thang Nguyen"},
    {name := "Quang Truong Nguyen"},
    {name := "Tobias Nipkow"},
    {name := "Steven Obua"},
    {name := "Joseph Pleso"},
    {name := "Jason Rute"},
    {name := "Alexey Solovyev"},
    {name := "Thi Hoai An Ta"},
    {name := "Nam Trung Tran"},
    {name := "Thi Diep Trieu"},
    {name := "Josef Urban"},
    {name := "Ky Vu"},
    {name := "Roland Zumkelle"}
  ],
 title := "A formal proof of the Kepler Conjecture",
 doi := "/10.1017/fmp.2017.1" }

-- TODO: provide the theorem number from the paper
unfinished Kepler_conjecture :
(∀ (V : set (vector ℝ 3)), packing V →
  (∃ (c : ℝ), ∀ (r : ℝ), (r ≥ 1) ->
  (↑(card(V ∩ open_ball origin₃ r)) ≤ pi* r^3/real_sqrt(18) + c*r^2))) :=
{ description := "Proof of Kepler conjecture",
  sources := [cite.Item (cite.Document hales_et_al_paper) "Theorem X.Y"] }

def Hales_T_et_al_Kepler_conj : fabstract :=
{ contributors := [{name := "Thomas Hales"}],
  description := "This article announces the formal proof of the Kepler conjecture on dense sphere packings in a combination of the HOL Light and Isabelle/HOL proof assistants.  It represents the primary result of the now completed Flyspeck project.",
  results := [result.Proof Kepler_conjecture]
}

end Hales_T_et_al_Kepler_conj
