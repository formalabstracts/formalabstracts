--open nat int
 
def isPrime (n : ℕ) : Prop :=
(n ≥ 2) ∧ (∀ m: ℕ, m ≥ 1 ∧ m ∣ n → ( m = 1 ∨ m = n) )
#print isPrime 

def infinite (s: set ℕ ): Prop :=
∀ n : ℕ, ∃ m ∈ s, n < m
#print infinite 

theorem TwicePrimeConjecture : 
infinite {n : ℕ  | isPrime n → isPrime (n + 2) ∨ isPrime (n - 2)} := sorry

#print TwicePrimeConjecture

theorem Goldbach'sConjecture : -- Thừa nhận , chưa được chứng minh
∀ n : ℕ, n > 2 ∧ 2 ∣ n 
→ ∃ a b : ℕ, isPrime a ∧ isPrime b ∧ n = a + b
:= sorry

#print Goldbach'sConjecture

theorem formPrime :
infinite {x: ℕ| ∃ n : ℕ, n > 0 ∧ x = n^2 + 1 ∧ isPrime x} := sorry

#print formPrime

--This also means there would be at least two primes between x2 and (x + 1)2 (one in the range from x2 to x(x + 1) and the second in the range from x(x + 1) to (x + 1)2)
theorem OppermanConjecture : 
∀ n : ℕ, ∃ a : ℕ, isPrime a ∧ n^2 < a ∧ a < (n + 1)^2 := sorry 

#print OppermanConjecture

theorem PolignacConjecture :
∀ n : ℕ, 2 ∣ n → infinite { a |isPrime a  →  isPrime (a + n) ∨ isPrime (a -n)} := sorry
#print PolignacConjecture
