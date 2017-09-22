-- complex numbers 

import data.set meta_data data.list data.vector .real_axiom

noncomputable theory

namespace complex 

open set classical nat int list vector real_axiom
local attribute [instance] prop_decidable
universe u

structure ℂ : Type :=
(re : ℝ) (im : ℝ)

@[instance] constant complex_field : field ℂ

attribute [instance] complex_field

def re (c : ℂ) := c.re

def im (c : ℂ) := c.im

def cx (a : ℝ) : ℂ := { re := a, im := 0 }

def cx2 (a : ℝ × ℝ)  : ℂ := { re := prod.fst a, im := prod.snd a }

def i : ℂ := { re := 0, im := 1 }

-- instance real_of_nat_coe : has_coe ℤ ℝ :=
-- ⟨ real_of_int ⟩

instance coe_real_complex : has_coe ℝ ℂ := 
⟨ cx ⟩

instance coe_real2_complex : has_coe (ℝ × ℝ) ℂ :=
⟨ cx2 ⟩

-- instance coe_complex_has_zero : has_zero ℂ :=
-- ⟨ cx 0 ⟩

-- instance coe_complex_has_one : has_one ℂ :=
-- ⟨ cx 1 ⟩

-- instance coe_complex_has_add : has_add ℂ :=
-- ⟨ λ c d, cx2(c.re + d.re,c.im + d.im) ⟩

-- instance coe_complex_has_mul : has_mul ℂ :=
-- ⟨ λ c d, cx2(c.re * d.re - c.im * d.im, c.re * d.im + c.im * d.re) ⟩

-- reserve infix ` ^. `: 80

-- instance coe_has_inv : has_inv ℂ :=
-- ⟨ λ z, cx2( z.re / (z.re ** 2  + z.im ** 2), - z.im / (z.re ** 2 + z.im ** 2) ) ⟩

local infix `^` := real_pow

def complex_pow : ℂ → ℕ → ℂ
 | x 0 :=  (1 : ℂ)
 | x (succ n) := x * (complex_pow x n)

-- complex conjugation
def cnj (z : ℂ) : ℂ :=
{ re := z.re, im := - z.im }

def norm (z : ℂ) : ℝ :=
real_sqrt (z.re ^ 2 + z.im ^ 2)

-- complex square root with branch along the negative real axis.
def csqrt (z : ℂ) : ℂ :=
if z.im = 0 then 
  if 0 ≤ z.re then cx(real_sqrt(z.re)) else cx2(0,real_sqrt(- z.re))
  else cx2(real_sqrt((norm z + z.re) / 2),(z.im/real_abs(z.im))*real_sqrt((norm z - z.re)/2))

def real (z: ℂ) :=
(z.im = 0)

-- cproduct

-- local infix `^` := complex_pow

end complex


