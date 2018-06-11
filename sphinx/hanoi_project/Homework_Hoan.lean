-- Nguyen Duc Hoan --
---------------------


--Twin Prime Conjecture

def infinite (s : set ℕ) : Prop := ∀ n : ℕ, ∃ m ∈ s, n < m

def isPrime (n : ℕ) : Prop := (n ≥ 2) ∧ (∀ m : ℕ, m ≥ 1 ∧ m ∣ n → (m = 1 ∨ m =n))

def is_pair_Primes (p:nat) :Prop := isPrime p ∧ isPrime (p+2)

#print is_pair_Primes

def the_set_of_pair_primes := { p:nat | is_pair_Primes p}

theorem Thm_Twin_Prime_Conj : infinite the_set_of_pair_primes :=
begin
 admit,
end 

------------------------------------------------
--Theorem n^2+1 Conjecture

theorem The_n2_plus_1_prime_Thm : 
infinite { p:ℕ | isPrime p ∧ ( ∃ n: nat, p = n*n + 1)} :=
begin
admit,
end 

-------------------------------------------------
--Goldbach’s Conjecture--

def isEven (n:nat) : Prop := n> 1 ∧ (2 ∣ n)

theorem Goldbach_Conjecture (n:nat) : isEven n → ∃ (p1: ℕ)  (p2 : ℕ), isPrime p1 ∧ isPrime p2 ∧  n = p1 + p2 :=
begin
admit,
end