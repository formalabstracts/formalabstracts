import meta_data

namespace Green_B_and_Tao_T_ArithmeticProgressionsInPrimes

def prime (n : nat) : Prop := n > 1 ∧ (∀ m < n, (m = 0) ∨ (m = 1) ∨ (n % m ≠ 0))

-- A statement of Green & Tao's theorem about arithmetic progressions in primes
axiom arithmetic_progressions_in_primes :
∀ n k : nat, ∃ m ≥ n, ∃ r ≥ 1, ∀ i < k, prime (m + i * r)

-- They also prove various stronger statements; this is an important and easy to state consequence.

definition green_tao_doc : document :=
{ authors := [{name := "Ben Green"}, {name := "Terry Tao"}],
  title := "The primes contain arbitrarily long arithmetic progressions",
  doi := "10.4007/annals.2008.167.481" }

def fabstract : fabstract :=
{ description := "The primes contain arbitrarily long arithmetic progressions",
  contributors := [{name := "Scott Morrison"}],
  results := [result.Proof arithmetic_progressions_in_primes],
  sources := [cite.Document green_tao_doc] }

end Green_B_and_Tao_T_ArithmeticProgressionsInPrimes
