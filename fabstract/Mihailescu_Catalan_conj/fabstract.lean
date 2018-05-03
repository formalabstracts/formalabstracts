import meta_data

namespace Mihailescu_P_Catalan_Conjecture

-- A statement of the catalan conjecture, with necessary conditions of nontriviality.

axiom catalan_conjecture :
∀ x y p q: nat, ((x > 0) ∧ (y > 0) ∧ (p ≠ 1) ∧ (q ≠ 1)) ∧ (x ^ p - y ^ q = 1) → (x = 3) ∧ (p = 2) ∧ (y = 2) ∧ (q = 3)

-- The complete algebraic proof was published by Mihăilescu in 2004, two years after he first proved the conjecture.

definition mihailescu_doc : document :=
{ authors := [{name := "Preda Mihăilescu"}],
  title := "Primary cyclotomic units and a proof of Catalans conjecture",
  doi := "10.1515/crll.2004.048" }

def fabstract : fabstract :=
{ description := "Primary cyclotomic units and a proof of Catalans conjecture",
  contributors := [{name := "Andrew Tindall"}],
  results := [result.Proof catalan_conjecture],
  sources := [cite.Document mihailescu_doc] }

end Mihailescu_P_Catalan_Conjecture
