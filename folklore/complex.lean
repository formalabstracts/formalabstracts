

-- basic development of complex numbers and
-- transcendental functions following HOL-Light,
-- up to the statement of the Riemann hypothesis.

import data.set meta_data data.list data.vector 
       topology.real algebra.group_power topology.infinite_sum
       

noncomputable theory

open classical

local attribute [instance] prop_decidable

namespace nat

def fact : ℕ → ℕ 
 | 0 :=  1
 | (succ n) := (n+1) * fact n

postfix `!`:9001 := fact

def odd (m : ℕ) : Prop :=
(∃ k, m = 2*k+1)

end nat

open set classical nat int list  monoid vector real

namespace real

unfinished sup : (set ℝ) → ℝ :=
{ description := "the supremum of a subset of real numbers.  It is undefined on the empty set and on sets unbounded above." }

def inf (S : set ℝ) : ℝ :=
- sup { x | S(-x) }

def sqrt (x : ℝ) : ℝ :=
   sup { t | (t = 0) ∨ t*t = x }

def abs (x : ℝ) : ℝ :=
  sup { t | t = x ∨ t = -x }

def max (x y : ℝ) : ℝ :=
  sup { t | t = x ∨ t = y }

def min (x y : ℝ) :=
  inf { t | t = x ∨ t = y }

end real

namespace complex 

open set classical nat int list vector real

local attribute [instance] prop_decidable

structure ℂ : Type :=
(re : ℝ) (im : ℝ)

@[instance] constant complex_field : field ℂ

attribute [instance] complex_field

def re (c : ℂ) := c.re

def im (c : ℂ) := c.im

def cx (a : ℝ) : ℂ := { re := a, im := 0 }

def cx2 (a : ℝ × ℝ)  : ℂ := { re := prod.fst a, im := prod.snd a }

def i : ℂ := { re := 0, im := 1 }

instance coe_real_complex : has_coe ℝ ℂ := 
⟨ cx ⟩

-- complex conjugation
def cnj (z : ℂ) : ℂ :=
{ re := z.re, im := - z.im }

def abs (z : ℂ) : ℝ :=
real.sqrt (z.re ^ 2 + z.im ^ 2)

-- complex square root with branch along the negative real axis
-- following HOL-Light
def sqrt (z : ℂ) : ℂ :=
if z.im = 0 then 
  if 0 ≤ z.re then cx(real.sqrt(z.re)) else cx2(0,real.sqrt(- z.re))
  else cx2(real.sqrt((abs z + z.re) / 2),(z.im/real.abs(z.im))*real.sqrt((abs z - z.re)/2))

def is_real (z: ℂ) :=
(z.im = 0)

instance : has_div ℂ := ⟨ λ x y, x * y⁻¹⟩

instance : has_zero ℂ := ⟨ (of_rat 0) ⟩

instance : has_one ℂ := ⟨of_rat 1⟩

instance inhabited_ℂ : inhabited ℂ := ⟨0⟩

open nat complex

constant complex_topology : topological_space ℂ

instance : topological_space ℂ := complex_topology

constant tam : topological_add_monoid ℂ

instance : topological_add_monoid ℂ := tam

def complex_sum (f : ℕ → ℂ) : ℂ := @tsum ℂ ℕ _ complex_topology _ f

notation `Σ` := complex_sum

instance real_of_nat_coe : has_coe ℚ ℝ := ⟨ of_rat ⟩

def exp (z : ℂ) : ℂ := Σ  (λ n, z^n / (n!) )

def cos (z : ℂ) : ℂ := (exp(i*z) + exp(-i*z))/2

def sin (z : ℂ) : ℂ := (exp(i*z) - exp(-i*z))/(2*i)

def tan (z : ℂ) := sin z / cos z

end complex

open complex classical

def real.exp (x : ℝ) : ℝ := re (complex.exp x)

def real.sin (x : ℝ) : ℝ := re (complex.sin x)

def real.cos (x : ℝ) : ℝ := re (complex.cos x)

def real.tan (x : ℝ) : ℝ := re (complex.tan x)

open real

-- log extended by 0 on non-positive reals
def real.log (y : ℝ) : ℝ := 
sup { x | (real.exp x = y) ∨ (x = 0 ∧ y ≤ 0) }

-- π is the smallest positive root of sin
def real.π : ℝ := 
real.inf { pi | 0 < pi ∧ real.sin pi = 0 }

open real

axiom log_exists (z : complex.ℂ) : 
(∃! w, (z = 0 ∧ w = 0) ∨ 
  ((z ≠ 0) ∧ complex.exp w = z ∧ -π < im w ∧ im w ≤ π))

def complex.arg (z : ℂ) : ℂ := 
real.inf { t | 0 ≤ t ∧ t < 2*π ∧ z = complex.abs(z)* exp(i*t) }

def complex.log (z : ℂ) : ℂ := classical.some (log_exists z)

-- w^z
def complex.pow (w : ℂ) (z : ℂ) : ℂ := 
if (w = 0) then 0 else exp (z * complex.log w)

def complex.atn (z : ℂ) : ℂ :=
(i / 2) * complex.log ( (1 - i * z) / (1 + i * z))

def complex.asn (z : ℂ) : ℂ :=
-i * complex.log(i * z + sqrt(1 - z^2))

def complex.acs (z : ℂ) : ℂ :=
-i * complex.log(z + i* sqrt(1 - z^2))

def real.asn (x : ℝ) : ℝ := re (complex.asn x)

def real.acs (x : ℝ) : ℝ := re (complex.acs x)

def real.sgn (x : ℝ) : ℝ := 
 if (x > 0) then 1
 else (if x = 0 then 0 else -1)

open real

-- nth root, extended to be an odd function:
def real.root (n : ℕ) (x : ℝ) : ℝ :=
sgn(x) * real.exp (real.log(real.abs x) / n)

-- HOL-Light's definition:
def real.pow (x : ℝ) (y : ℝ) : ℝ :=
let exlog y x := real.exp(y * real.log x) in
if (x > 0) then exlog y x 
else if (x = 0) then (if y = 0 then 1 else 0)
else if (∃ (m n : ℕ), real.abs y = m / n ∧ odd m ∧ odd n) 
     then - exlog y (-x)
else exlog y (-x)

open filter

/-
1-dimensional complex case of Frechet derivative.
We take f here to be total, 
but the derivative depends only on its germ at z0.
-/

def has_complex_derivative_at 
(f : ℂ → ℂ)
(f'z : ℂ) 
(z : ℂ) : Prop :=
let error_term (h : ℂ) : ℝ := 
    abs((f (z + h) - (f z + f'z * h))/h) in
(tendsto error_term (nhds 0) (nhds 0))

-- This must be already defined somewhere. But where?
def to_subtype {α : Type*} (p : α → Prop) (x : α) (h : p x) :
subtype p :=
{ val := x, property := h }

def extend_by_zero 
(domain : set ℂ) (f : subtype domain → ℂ) (z : ℂ) : ℂ :=
if h: domain z then f (to_subtype domain z h) else 0

def holomorphic_on (domain : set ℂ) (f : subtype domain → ℂ) :=
(∀ z : subtype domain, ∃ f'z,
  has_complex_derivative_at (extend_by_zero domain f) f'z z)

class holomorphic_function :=
(domain : set ℂ)
(f : subtype domain → ℂ) 
(open_domain : is_open domain)
(has_derivative : holomorphic_on domain f)

-- notation f(z), for holomorphic functions
instance : has_coe_to_fun holomorphic_function :=
{ F := λ h, subtype h.domain → ℂ, coe := λ h, h.f }

-- converges for Re(s) > 1
def riemann_zeta_sum (s : ℂ) : ℂ :=
Σ  (λ n,  complex.pow n  (-s) )

-- trivial zeros at -2, -4, -6,...
def riemann_zeta_trivial_zero (s : ℂ) : Prop :=
(∃ n : ℕ, n > 0 ∧ s = (-2)*n)

-- analytic continuation of Riemann zeta function.
axiom riemann_zeta_exists :
(∃! ζ : holomorphic_function, ζ.domain = (set.univ \ {1}) ∧
  ∀ s : subtype ζ.domain, re(s) > 1 → ζ(s) = riemann_zeta_sum s)

def ζ := classical.some riemann_zeta_exists

--  (s ≠ 1) implicit in the domain constraints:
def riemann_hypothesis :=
(∀ s, ζ(s) = 0 ∧ ¬(riemann_zeta_trivial_zero s) →
re (s) = 1/2)
