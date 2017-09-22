import meta_data
       .turing_machines

namespace Cook_S_P_NP

/- Definitions of the complexity classes P and NP -/

def NP_computable (f : list bool → list bool) : Prop :=
∃ s n (TM : NTATM s n) (c k : nat),
  computes_fn_in_time
    TM
    (λ i : fin 1 → list bool, f (i 0))
    (λ i, c * ((i 0).length^k + 1))

def P_computable (f : list bool → list bool) : Prop :=
∃ s n (TM : TATM s n) (c k : nat),
  @computes_fn_in_time
    s n TM _
    (λ i : fin 1 → list bool, f (i 0))
    (λ i, c * ((i 0).length^k + 1))

-- NP: nondeterministic polynomial time computable problems
def NP : set (set (list bool)) :=
{ L | ∃ D : decidable_pred L, NP_computable (λ x, [@to_bool _ (D x)]) }

-- P: deterministic polynomial time computable problems
def P : set (set (list bool)) :=
{ L | ∃ D : decidable_pred L, P_computable (λ x, [@to_bool _ (D x)]) }

inductive prop
| true : prop
| false : prop
| var : nat → prop
| not : prop → prop
| and : prop → prop → prop
| or : prop → prop → prop

def encode_nat (n : nat) : list bool :=
(do b ← n.bits, [tt, b]) ++ [ff]

def encode_prop : prop → list bool
| prop.true := encode_nat 0
| prop.false := encode_nat 1
| (prop.var i) := encode_nat 2 ++ encode_nat i
| (prop.not a) := encode_nat 3 ++ encode_prop a
| (prop.and a b) := encode_nat 4 ++ encode_prop a ++ encode_prop b
| (prop.or a b) := encode_nat 5 ++ encode_prop a ++ encode_prop b

def eval (v : nat → bool) : prop → bool
| prop.true := tt
| prop.false := ff
| (prop.var i) := v i
| (prop.not a) := bnot (eval a)
| (prop.and a b) := eval a && eval b
| (prop.or a b) := eval a || eval b

/- Boolean satisfiability problem -/
def SAT : set (list bool) :=
{ x | ∃ p v, encode_prop p = x ∧ eval v p = tt }

/- SAT is in NP -/
unfinished SAT_NP : SAT ∈ NP :=
{ description := "SAT is an NP-problem",
  sources := [cite.Website "TODO(@digama0)"] }

def P_reducible (L₁ L₂ : set (list bool)) : Prop :=
∃ f, P_computable f ∧ L₁ = {x | f x ∈ L₂}

/- Any problem in NP can be polynomial-time reduced to SAT -/
unfinished SAT_reducibility : ∀ L ∈ NP, P_reducible L SAT :=
{ description := "Any problem in NP can be polynomial-time reduced to SAT",
  sources := [cite.Website "TODO(@digama0)"] }

def fabstract : fabstract :=
{ description := "A conjecture that the complexity classes P and NP are unequal.",
  contributors := [{name := "Mario Carneiro"}],
  sources :=[cite.Document {title := "The Complexity of theorem-proving procedures", authors := [{name := "Stephen Cook"}], doi := "10.1145/800157.805047"}],
  results := [result.Proof SAT_NP,
              result.Proof SAT_reducibility,
              result.Conjecture (P ≠ NP)] }

end Cook_S_P_NP
