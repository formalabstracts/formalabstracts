import .turing_machines ...meta_data

namespace Cook_S_P_NP

/- Definitions of the complexity classes P and NP -/

-- NP: nondeterministic polynomial time computable problems
def NP : set (set (list bool)) := λ L,
∃ D : decidable_pred L,
let f : (fin 1 → list bool) → list bool :=
λ i, [@to_bool _ (D (i 0))] in
∃ s n (TM : NTATM s n) (c k : nat),
computes_fn_in_time TM f $ λ i, c * ((i 0).length^k + 1)

-- P: deterministic polynomial time computable problems
def P : set (set (list bool)) := λ L,
∃ D : decidable_pred L,
let f : (fin 1 → list bool) → list bool :=
λ i, [@to_bool _ (D (i 0))] in
∃ s n (TM : TATM s n) (c k : nat),
@computes_fn_in_time s n TM _ f $ λ i, c * ((i 0).length^k + 1)

/- Boolean satisfiability problem -/
axiom SAT : set (list bool)

/- SAT is in NP -/
axiom SAT_NP : SAT ∈ NP

/- SAT is in NP -/
axiom P_reducible (L₁ L₂ : set (list bool)) : Prop

/- Any problem in NP can be polynomial-time reduced to SAT -/
axiom SAT_reducibility : ∀ L ∈ NP, P_reducible L SAT

open result
def fabstract : meta_data := {
  description := "A conjecture that the complexity classes P and NP are unequal.",
  authors := ["Stephen A. Cook"],
  doi := ["https://doi.org/10.1145/800157.805047"],
  results := [Proof SAT_NP,
              Proof SAT_reducibility,
              Conjecture (P ≠ NP)]
}

end Cook_S_P_NP
